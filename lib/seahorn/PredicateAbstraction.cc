#include "seahorn/PredicateAbstraction.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornClauseDB.hh"

#include "seahorn/HornDbModel.hh"
#include "seahorn/HornModelConverter.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include <vector>
#include <boost/logic/tribool.hpp>
#include "seahorn/HornClauseDBWto.hh"
#include <algorithm>
#include <fstream>
#include <iostream>

#include "ufo/Stats.hh"

using namespace llvm;

namespace seahorn
{
	char PredicateAbstraction::ID = 0;

	bool PredicateAbstraction::runOnModule (Module &M)
	{
		HornifyModule &hm = getAnalysis<HornifyModule> ();

		PredicateAbstractionAnalysis pabs(hm);
		pabs.runAnalysis();

		return false;
	}

	void PredicateAbstraction::getAnalysisUsage (AnalysisUsage &AU) const
	{
		AU.addRequired<HornifyModule> ();
		AU.setPreservesAll();
	}

	void PredicateAbstractionAnalysis::runAnalysis()
	{
		Stats::resume ("Pabs solve");
		//load the Horn clause database
		auto &db = m_hm.getHornClauseDB ();
		db.buildIndexes ();

		//guess candidates
		guessCandidate(db);

		HornDbModel oldModel;

		PredAbsHornModelConverter converter;

		//run main algorithm
		HornClauseDB new_db = generateAbstractDB(db, converter);

		//initialize spacer based on new DB
		m_fp.reset (new ZFixedPoint<EZ3> (m_hm.getZContext ()));
		ZFixedPoint<EZ3> &fp = *m_fp;
		ZParams<EZ3> params (m_hm.getZContext ());
		params.set (":engine", "spacer");
		// -- disable slicing so that we can use cover
		params.set (":xform.slice", false);
		params.set (":use_heavy_mev", true);
		params.set (":reset_obligation_queue", true);
		params.set (":pdr.flexible_trace", false);
		params.set (":xform.inline-linear", false);
		params.set (":xform.inline-eager", false);
		// -- disable utvpi. It is unstable.
		params.set (":pdr.utvpi", false);
		// -- disable propagate_variable_equivalences in tail_simplifier
		params.set (":xform.tail_simplifier_pve", false);
		params.set (":xform.subsumption_checker", true);
//		params.set (":order_children", true);
//		params.set (":pdr.max_num_contexts", "500");
		fp.set (params);
		new_db.loadZFixedPoint (fp, false);
		boost::tribool result = fp.query ();

		LOG("pabs-smt2", outs() << "SMT2: " << fp << "\n";);

		if (result) outs () << "sat";
		else if (!result)
		{
			outs() << "unsat\n";
			HornDbModel absModel;
			initAbsModelFromFP(absModel, new_db, fp);

			converter.convert(absModel, oldModel);
			LOG("pabs-debug", outs() << "FINAL RESULT:\n";);
			//Print invariants
			printInvars(db, oldModel);
		}
		else outs () << "unknown";
		outs () << "\n";
		Stats::stop("Pabs solve");
	}

	void PredicateAbstractionAnalysis::initAbsModelFromFP(HornDbModel &absModel, HornClauseDB &db, ZFixedPoint<EZ3> &fp)
	{	//How to iterate over all predicates in DB?
		ExprVector all_preds_in_DB;
		for(HornRule r : db.getRules())
		{
			Expr pred = r.head();
			all_preds_in_DB.push_back(pred);
		}
		for(Expr pred : all_preds_in_DB)
		{
			LOG("pabs-debug", outs() << "REL: " << *(bind::fname(pred)) << "\n";);
			Expr solution = fp.getCoverDelta(pred);
			LOG("pabs-debug", outs() << "SOLUTION: " << *solution << "\n";);
			absModel.addDef(pred, solution);
		}
	}

	HornClauseDB PredicateAbstractionAnalysis::generateAbstractDB(HornClauseDB &db, PredAbsHornModelConverter &converter)
	{
		HornClauseDB new_DB(db.getExprFactory ());

		generateAbstractRelations(db, new_DB, converter);

		generateAbstractRules(db, new_DB, converter);

		generateAbstractQueries(db, new_DB);

		LOG("pabs-debug", outs() << "NEW DB: \n";);
		LOG("pabs-debug", outs() << new_DB << "\n";);

		converter.setAbsDB(new_DB); //set converter

		return new_DB;
	}

	void PredicateAbstractionAnalysis::generateAbstractRelations(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter)
	{
		//For each relation, generate its abstract version
		for(Expr rel : db.getRelations())
		{
			LOG("pabs-debug", outs() << "OLD REL: " << *rel << "\n";);
			ExprVector new_args;
			//Push fdecl name
			Expr old_fdecl_name = bind::fname(rel);
			std::ostringstream oss;
			oss << old_fdecl_name << "_pabs";
			new_args.push_back(old_fdecl_name);
			//Push boolean types
			ExprVector term_vec = currentCandidates.find(rel)->second;
			if(term_vec.size() > 1 || term_vec.size() == 1 && !isOpX<TRUE>(term_vec[0]))
			{
				for(int i=0; i<term_vec.size(); i++)
				{
					new_args.push_back(mk<BOOL_TY>(rel->efac()));
				}
			}
			else // the candidate term is just 'true' or 'false'
			{
				for (int i=1; i<=bind::domainSz(rel); i++ )
				{
					new_args.push_back(bind::domainTy(rel, i));
				}
			}
			//Push return type
			new_args.push_back(bind::rangeTy(rel));
			Expr new_rel = mknary<FDECL>(new_args);

			//new pred name
			Expr new_fdecl_name = mkTerm<std::string>(oss.str(), new_rel->efac());
			new_rel = bind::rename(new_rel, new_fdecl_name);

			LOG("pabs-debug", outs() << "NEW REL: " << *new_rel << "\n";);
			new_DB.registerRelation(new_rel);

			oldToNewPredMap.insert(std::pair<Expr, Expr>(rel, new_rel));
			newToOldPredMap.insert(std::pair<Expr, Expr>(new_rel, rel));
		}
		converter.setNewToOldPredMap(newToOldPredMap); //set converter
	}

	void PredicateAbstractionAnalysis::generateAbstractRules(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter)
	{
		for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
		{
			HornRule r = *it;
			LOG("pabs-debug", outs() << "OLD RULE HEAD: " << *(r.head()) << "\n";);
			LOG("pabs-debug", outs() << "OLD RULE BODY: " << *(r.body()) << "\n";);

			//old rule variables
			ExprVector rule_vars;
			rule_vars.insert(rule_vars.end(), r.vars().begin(), r.vars().end());

			//Map for counting occurrence time for each relation in per rule
			std::map<Expr, int> relOccurrenceTimesMap;

			ExprVector pred_vector;
			HornDbUtils::get_all_pred_apps(r.body(), db, std::back_inserter(pred_vector));
			pred_vector.push_back(r.head());

			//Deal with the rules that have no predicates
			if(!HornDbUtils::hasBvarInRule(r, db, currentCandidates))
			{
				ExprMap replaceMap;
				for(Expr pred : pred_vector)
				{
					Expr new_fdecl = oldToNewPredMap.find(bind::fname(pred))->second;
					Expr new_pred = bind::reapp(pred, new_fdecl);
					replaceMap.insert(std::pair<Expr, Expr>(pred, new_pred));
				}
				Expr new_head = replace(r.head(), replaceMap);
				Expr new_body = replace(r.body(), replaceMap);
				HornRule new_rule(r.vars(), new_head, new_body);
				new_DB.addRule(new_rule);
				continue;
			}

			//initialize the occurrence count map
			for(ExprVector::iterator it = pred_vector.begin(); it!= pred_vector.end(); ++it)
			{
				relOccurrenceTimesMap.insert(std::pair<Expr, int>(bind::fname(*it), 0));
			}

			//construct new body
			ExprVector new_body_exprs;

			//For each predicate in the body, construct new version of predicate.
			Expr rule_body = r.body();
			ExprVector body_pred_apps;
			HornDbUtils::get_all_pred_apps(rule_body, db, std::back_inserter(body_pred_apps));
			for(ExprVector::iterator it = body_pred_apps.begin(); it != body_pred_apps.end(); ++it)
			{
				Expr rule_body_pred = *it;
				Expr new_rule_body_rel = oldToNewPredMap.find(bind::fname(rule_body_pred))->second;

				int pred_order = relOccurrenceTimesMap.find(bind::fname(rule_body_pred))->second;
				relOccurrenceTimesMap[bind::fname(rule_body_pred)] += 1;

				ExprVector new_rule_body_args;
				//Push boolean variables into arguments of new predicate

				for(int i=0; i<bind::domainSz(new_rule_body_rel); i++)
				{
					Expr var_tag = variant::variant(pred_order, variant::variant(i, variant::tag(bind::fname(new_rule_body_rel), mkTerm<std::string> ("p", new_rule_body_rel->efac ())))); //noprime
					Expr boolVar = bind::boolConst(var_tag);
					rule_vars.push_back(boolVar);
					new_rule_body_args.push_back(boolVar);
				}

				Expr new_rule_body_pred = bind::fapp(new_rule_body_rel, new_rule_body_args);
				new_body_exprs.push_back(new_rule_body_pred);

				//for each predicate in the body, create iff
				if(bind::domainSz(bind::fname(new_rule_body_pred)) == 0)
				{
					continue;
				}
				int index = 0;
				//for converter
				ExprMap boolToTermMap;
				for(Expr term : currentCandidates.find(bind::fname(*it))->second)
				{
					Expr term_app = HornDbUtils::applyArgsToBvars(term, *it, currentCandidates);
					Expr equal_expr = mk<IFF>(new_rule_body_pred->arg(index + 1), term_app);
					//converter
					boolToTermMap.insert(std::pair<Expr, Expr>(bind::bvar(index, mk<BOOL_TY>(term_app->efac())), term));

					new_body_exprs.push_back(equal_expr);
					index ++;
				}
				converter.addRelToBoolToTerm(bind::fname(*it), boolToTermMap);
				//converter.getRelToBoolToTermMap().insert(std::pair<Expr, ExprMap>(bind::fname(*it), boolToTermMap));
			}

			Expr rule_head = r.head();

			//construct new rule head.
			Expr new_rule_head_rel = oldToNewPredMap.find(bind::fname(rule_head))->second;

			ExprVector new_rule_head_args;
			int pred_order = relOccurrenceTimesMap.find(bind::fname(rule_head))->second;
			relOccurrenceTimesMap[bind::fname(rule_head)] += 1;
			for(int i=0; i<bind::domainSz(new_rule_head_rel); i++)
			{
				Expr var_tag = variant::variant(pred_order, variant::variant(i, variant::tag(bind::fname(new_rule_head_rel), mkTerm<std::string> ("p", new_rule_head_rel->efac ())))); //prime
				Expr boolVar = bind::boolConst(var_tag);
				rule_vars.push_back(boolVar);
				new_rule_head_args.push_back(boolVar);
			}

			Expr new_rule_head = bind::fapp(new_rule_head_rel, new_rule_head_args);
			LOG("pabs-debug", outs() << "NEW RULE HEAD: " << *new_rule_head << "\n";);


			if(bind::domainSz(bind::fname(rule_head)) != 0)
			{
				//construct head equality expr, put in new body
				int index = 0;
				//for converter
				ExprMap boolToTermMap;
				for(Expr term : currentCandidates.find(bind::fname(rule_head))->second)
				{
					Expr term_app = HornDbUtils::applyArgsToBvars(term, rule_head, currentCandidates);
					Expr equal_expr = mk<IFF>(new_rule_head->arg(index + 1), term_app);
					//converter
					boolToTermMap.insert(std::pair<Expr, Expr>(bind::bvar(index, mk<BOOL_TY>(term_app->efac())), term));

					new_body_exprs.push_back(equal_expr);
					index ++;
				}
				converter.addRelToBoolToTerm(bind::fname(rule_head), boolToTermMap);
				//converter.getRelToBoolToTermMap().insert(std::pair<Expr, ExprMap>(bind::fname(rule_head), boolToTermMap));
			}

			//Extract the constraints
			Expr constraints = HornDbUtils::extractTransitionRelation(r, db);
			new_body_exprs.push_back(constraints);

			//Construct new body
			Expr new_rule_body = mknary<AND>(new_body_exprs.begin(), new_body_exprs.end());
			LOG("pabs-debug", outs() << "NEW RULE BODY :" << *new_rule_body << "\n";);

			HornRule new_rule(rule_vars, new_rule_head, new_rule_body);
			new_DB.addRule(new_rule);
		}
	}

	void PredicateAbstractionAnalysis::generateAbstractQueries(HornClauseDB &db, HornClauseDB &new_DB)
	{
		for(auto old_query : db.getQueries())
		{
			Expr old_fdecl = bind::fname(old_query);
			Expr new_fdecl = oldToNewPredMap.find(old_fdecl)->second;
			ExprVector old_args;
			Expr new_query = bind::fapp(new_fdecl, old_args);
			new_DB.addQuery(new_query);
		}
	}

	void PredicateAbstractionAnalysis::guessCandidate(HornClauseDB &db)
	{
	  for(Expr rel : db.getRelations())
	  {
		  if(bind::isFdecl(rel))
		  {
			  //ExprVector terms = relToCand(rel);
			  ExprVector terms = applyTemplatesFromExperimentFile(rel, "/home/chenguang/Desktop/seahorn/experiment/preds_temp");
			  currentCandidates.insert(std::pair<Expr, ExprVector>(rel, terms));
		  }
	  }
	}

	ExprVector PredicateAbstractionAnalysis::applyTemplatesFromExperimentFile(Expr fdecl, std::string filepath)
	{
		ExprVector bvars;
		ExprVector lemmas;

		int bvar_count = 0;
		for(int i=0; i<bind::domainSz(fdecl); i++)
		{
			if(isOpX<INT_TY>(bind::domainTy(fdecl, i)))
			{
				Expr bvar = bind::bvar(i, mk<INT_TY>(bind::domainTy(fdecl, i)->efac()));
				bvars.push_back(bvar);
				bvar_count ++;
			}
		}
		Expr one = mkTerm<mpz_class> (1, fdecl->efac());
		Expr zero = mkTerm<mpz_class> (0, fdecl->efac());
		Expr two = mkTerm<mpz_class> (2, fdecl->efac());
		if(bvar_count == 0)
		{
			lemmas.push_back(mk<TRUE>(fdecl->efac()));
		}
		else if(bvar_count == 1)
		{
			lemmas.push_back(mk<GEQ>(bvars[0], one));
			lemmas.push_back(mk<LEQ>(bvars[0], one));
			lemmas.push_back(mk<GEQ>(bvars[0], zero));
			lemmas.push_back(mk<GEQ>(bvars[0], two));
			lemmas.push_back(mk<LEQ>(bvars[0], two));
			parseLemmasFromExpFile(bvars[0], lemmas, filepath);
		}
		else
		{
			for(int i=0; i<bvars.size(); i++)
			{
				lemmas.push_back(mk<GEQ>(bvars[i], one));
				lemmas.push_back(mk<LEQ>(bvars[i], one));
				lemmas.push_back(mk<GEQ>(bvars[i], zero));
				lemmas.push_back(mk<GEQ>(bvars[i], two));
				lemmas.push_back(mk<LEQ>(bvars[i], two));
				parseLemmasFromExpFile(bvars[i], lemmas, filepath);
			}
		}
		return lemmas;
	}

	void PredicateAbstractionAnalysis::parseLemmasFromExpFile(Expr bvar, ExprVector& lemmas, std::string filepath)
	{
		std::ifstream in(filepath);
		std::string line;
		if(in)
		{
			while (getline (in, line))
			{
				std::string op = HornDbUtils::split(line, ",")[0];
				std::string number = HornDbUtils::split(line, ",")[1];
				int value = std::atoi(number.c_str());
				if(op == "LEQ") lemmas.push_back(mk<LEQ>(bvar, mkTerm<mpz_class>(value, bvar->efac())));
				else if(op == "GEQ") lemmas.push_back(mk<GEQ>(bvar, mkTerm<mpz_class>(value, bvar->efac())));
				else if(op == "LT") lemmas.push_back(mk<LT>(bvar, mkTerm<mpz_class>(value, bvar->efac())));
				else if(op == "GT") lemmas.push_back(mk<GT>(bvar, mkTerm<mpz_class>(value, bvar->efac())));
			}
		}
		else
		{
			errs() << "FILE NOT EXIST!\n";
			return;
		}
	}

	ExprVector PredicateAbstractionAnalysis::relToCand(Expr fdecl)
	{
		ExprVector bvars;
		ExprVector bins;   // a vector of LT expressions
		Expr cand = NULL;

		int bvar_count = 0;
		unsigned i = 0;
		for (i=0; i < bind::domainSz(fdecl); i++)
		{
			// if its type is INT
			if (isOpX<INT_TY>(bind::domainTy(fdecl, i)))
			{
				// what is efac?
				Expr bvar = bind::bvar (i, mk<INT_TY>(bind::domainTy(fdecl, i)->efac())); //the id of bvar is the same as related arg index
				bvars.push_back(bvar);
				bvar_count ++;
			}
		}

		//What if there's no bvar?
		if(bvar_count == 0)
		{
			bins.push_back(mk<TRUE>(fdecl->efac()));
		}
		// if there is only one bvar, create a int constant and make an lt expr
		else if(bvar_count == 1)
		{
			Expr one = mkTerm<mpz_class> (1, fdecl->efac());//
			bins.push_back(mk<GEQ>(bvars[0], one));//
			bins.push_back(mk<LEQ>(bvars[0], one));//
			Expr zero = mkTerm<mpz_class> (0, fdecl->efac());
			bins.push_back(mk<GEQ>(bvars[0], zero));//
			Expr two = mkTerm<mpz_class> (2, fdecl->efac());//
			bins.push_back(mk<GEQ>(bvars[0], two));//
			bins.push_back(mk<LEQ>(bvars[0], two));//
			//For test
//			bins.push_back(mk<GEQ>(bvars[0], five));//
//			bins.push_back(mk<GEQ>(bvars[0], six));//
//			bins.push_back(mk<GEQ>(bvars[0], seven));//
//			bins.push_back(mk<GEQ>(bvars[0], eight));//
//			bins.push_back(mk<GEQ>(bvars[0], nine));//
//			bins.push_back(mk<GEQ>(bvars[0], ten));//
//			bins.push_back(mk<GEQ>(bvars[0], eleven));//
//			bins.push_back(mk<GEQ>(bvars[0], twelve));//
//			bins.push_back(mk<GEQ>(bvars[0], thirteen));//
//			bins.push_back(mk<GEQ>(bvars[0], fourteen));//
//			bins.push_back(mk<GEQ>(bvars[0], fifteen));//
//			bins.push_back(mk<LEQ>(bvars[0], sixteen));//
//			bins.push_back(mk<LEQ>(bvars[0], seventeen));//
//			bins.push_back(mk<LEQ>(bvars[0], eighteen));//
//			bins.push_back(mk<LEQ>(bvars[0], nineteen));//
//			bins.push_back(mk<LEQ>(bvars[0], twenty));//
//			bins.push_back(mk<LEQ>(bvars[0], twenty_one));//
//			bins.push_back(mk<GT>(bvars[0], thirty));//
//			bins.push_back(mk<GT>(bvars[0], fourty));//
//			bins.push_back(mk<GT>(bvars[0], fifty));//
//			bins.push_back(mk<GT>(bvars[0], sixty));//
//			bins.push_back(mk<GT>(bvars[0], seventy));//
//			bins.push_back(mk<GT>(bvars[0], eighty));//
//			bins.push_back(mk<LT>(bvars[0], ninty));//
//			bins.push_back(mk<LT>(bvars[0], thirty));//
//			bins.push_back(mk<LEQ>(bvars[0], thirty));//
//			bins.push_back(mk<LEQ>(bvars[0], fourty));//
//			bins.push_back(mk<LEQ>(bvars[0], fifty));//
//			bins.push_back(mk<LT>(bvars[0], fifty));//
//			bins.push_back(mk<LT>(bvars[0], sixty));//
//			bins.push_back(mk<LEQ>(bvars[0], one_hundred));//
//			bins.push_back(mk<LEQ>(bvars[0], two_hundred));//
//			bins.push_back(mk<LT>(bvars[0], five));//
//			bins.push_back(mk<LT>(bvars[0], six));//
//			bins.push_back(mk<LT>(bvars[0], seven));//
//			bins.push_back(mk<LT>(bvars[0], eight));//
//			bins.push_back(mk<LT>(bvars[0], nine));//
//			bins.push_back(mk<LT>(bvars[0], ten));//
//			bins.push_back(mk<LT>(bvars[0], eleven));//
//			bins.push_back(mk<LT>(bvars[0], twelve));//
//			bins.push_back(mk<LT>(bvars[0], thirteen));//
//			bins.push_back(mk<LT>(bvars[0], fourteen));//
//			bins.push_back(mk<LT>(bvars[0], fifteen));//
//			bins.push_back(mk<LEQ>(bvars[0], three_hundred));//
//			bins.push_back(mk<LEQ>(bvars[0], four_hundred));//
//			bins.push_back(mk<LEQ>(bvars[0], five_hundred));//
//			bins.push_back(mk<LEQ>(bvars[0], six_hundred));//
//			bins.push_back(mk<LEQ>(bvars[0], seven_hundred));//
//			bins.push_back(mk<LEQ>(bvars[0], eight_hundred));//
//			bins.push_back(mk<LEQ>(bvars[0], nine_hundred));//
		}
		else // bvar_count >= 2
		{
//			for(int j=0; j<bvars.size()-1; j++)
//			{
//				Expr lt = mk<LT>(bvars[j], bvars[j+1]);
//				bins.push_back(lt);
//				//
//				bins.push_back(mk<GT>(bvars[j], bvars[j+1]));
//			}
			Expr one = mkTerm<mpz_class> (1, fdecl->efac());
			Expr zero = mkTerm<mpz_class> (0, fdecl->efac());
			Expr two = mkTerm<mpz_class> (2, fdecl->efac());//
			for(int j=0; j<bvars.size(); j++)
			{
				bins.push_back(mk<GEQ>(bvars[j], one));
				bins.push_back(mk<LEQ>(bvars[j], one));
				bins.push_back(mk<GEQ>(bvars[j], zero));
				bins.push_back(mk<GEQ>(bvars[j], two));//
				bins.push_back(mk<LEQ>(bvars[j], two));//
				//For test
//				bins.push_back(mk<GEQ>(bvars[j], five));//
//				bins.push_back(mk<GEQ>(bvars[j], six));//
//				bins.push_back(mk<GEQ>(bvars[j], seven));//
//				bins.push_back(mk<GEQ>(bvars[j], eight));//
//				bins.push_back(mk<GEQ>(bvars[j], nine));//
//				bins.push_back(mk<GEQ>(bvars[j], ten));//
//				bins.push_back(mk<GEQ>(bvars[j], eleven));//
//				bins.push_back(mk<GEQ>(bvars[j], twelve));//
//				bins.push_back(mk<GEQ>(bvars[j], thirteen));//
//				bins.push_back(mk<GEQ>(bvars[j], fourteen));//
//				bins.push_back(mk<GEQ>(bvars[j], fifteen));//
//				bins.push_back(mk<LEQ>(bvars[j], sixteen));//
//				bins.push_back(mk<LEQ>(bvars[j], seventeen));//
//				bins.push_back(mk<LEQ>(bvars[j], eighteen));//
//				bins.push_back(mk<LEQ>(bvars[j], nineteen));//
//				bins.push_back(mk<LEQ>(bvars[j], twenty));//
//				bins.push_back(mk<LEQ>(bvars[j], twenty_one));//
//				bins.push_back(mk<GT>(bvars[j], thirty));//
//				bins.push_back(mk<GT>(bvars[j], fourty));//
//				bins.push_back(mk<GT>(bvars[j], fifty));//
//				bins.push_back(mk<GT>(bvars[j], sixty));//
//				bins.push_back(mk<GT>(bvars[j], seventy));//
//				bins.push_back(mk<GT>(bvars[j], eighty));//
//				bins.push_back(mk<LT>(bvars[j], ninty));//
//				bins.push_back(mk<LT>(bvars[j], thirty));//
//				bins.push_back(mk<LEQ>(bvars[j], thirty));//
//				bins.push_back(mk<LEQ>(bvars[j], fourty));//
//				bins.push_back(mk<LEQ>(bvars[j], fifty));//
//				bins.push_back(mk<LT>(bvars[j], fifty));//
//				bins.push_back(mk<LT>(bvars[j], sixty));//
//				bins.push_back(mk<LEQ>(bvars[j], one_hundred));//
//				bins.push_back(mk<LEQ>(bvars[j], two_hundred));//
//				bins.push_back(mk<LT>(bvars[j], five));//
//				bins.push_back(mk<LT>(bvars[j], six));//
//				bins.push_back(mk<LT>(bvars[j], seven));//
//				bins.push_back(mk<LT>(bvars[j], eight));//
//				bins.push_back(mk<LT>(bvars[j], nine));//
//				bins.push_back(mk<LT>(bvars[j], ten));//
//				bins.push_back(mk<LT>(bvars[j], eleven));//
//				bins.push_back(mk<LT>(bvars[j], twelve));//
//				bins.push_back(mk<LT>(bvars[j], thirteen));//
//				bins.push_back(mk<LT>(bvars[j], fourteen));//
//				bins.push_back(mk<LT>(bvars[j], fifteen));//
//				bins.push_back(mk<LEQ>(bvars[j], three_hundred));//
//				bins.push_back(mk<LEQ>(bvars[j], four_hundred));//
//				bins.push_back(mk<LEQ>(bvars[j], five_hundred));//
//				bins.push_back(mk<LEQ>(bvars[j], six_hundred));//
//				bins.push_back(mk<LEQ>(bvars[j], seven_hundred));//
//				bins.push_back(mk<LEQ>(bvars[j], eight_hundred));//
//				bins.push_back(mk<LEQ>(bvars[j], nine_hundred));//
			}
		}

		return bins;
	}

	void PredicateAbstractionAnalysis::printInvars(HornClauseDB &db, HornDbModel &origModel)
	{
		//How to iterate all predicates?
		ExprMap relToAppMap;
		for(HornRule r : db.getRules())
		{
			Expr pred = r.head();
			relToAppMap.insert(std::pair<Expr, Expr>(bind::fname(pred), pred));
		}
		for(ExprMap::iterator it = relToAppMap.begin(); it!=relToAppMap.end(); ++it)
		{
			Expr pred = it->second;
			Expr def = origModel.getDef(pred);
			LOG("predabs", errs() << *bind::fname(bind::fname(pred)) << ": " << *def << "\n";);
		}
	}
}
