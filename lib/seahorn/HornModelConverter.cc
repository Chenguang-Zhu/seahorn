#include "seahorn/HornModelConverter.hh"
#include "seahorn/HornDbModel.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDB.hh"

#include "ufo/Expr.hpp"
#include <vector>

#include "ufo/Stats.hh"

namespace seahorn
{
	bool PredAbsHornModelConverter::convert (HornDbModel &in, HornDbModel &out)
	{
		for(Expr abs_rel : abs_db->getRelations())
		{
			LOG("pabs-debug", outs() << "ABS REL: " << *abs_rel << "\n";);

			Expr orig_rel = newToOldPredMap.find(abs_rel)->second;
			LOG("pabs-debug", outs() << "ORIG REL: " << *orig_rel << "\n";);

			ExprVector abs_arg_list;
			for(int i=0; i<bind::domainSz(abs_rel); i++)
			{
				Expr boolVar = bind::boolConst(variant::variant(i, mkTerm<std::string>("b", orig_rel->efac())));
				abs_arg_list.push_back(boolVar);
			}
			Expr abs_rel_app = bind::fapp(abs_rel, abs_arg_list);
			LOG("pabs-debug", outs() << "ABS REL APP: " << *abs_rel_app << "\n";);

			Expr abs_def_app = in.getDef(abs_rel_app);
			LOG("pabs-debug", outs() << "ABS DEF APP: " << *abs_def_app << "\n";);

			ExprMap boolVarToBvarMap;
			ExprVector bools;
			HornDbUtils::get_all_booleans(abs_def_app, std::back_inserter(bools));
			for(Expr boolvar: bools)
			{
				Expr bool_bvar = bind::boolBVar(variant::variantNum(bind::fname(bind::fname(boolvar))), boolvar->efac());
				boolVarToBvarMap.insert(std::pair<Expr,Expr>(boolvar, bool_bvar));
			}
			Expr abs_def = replace(abs_def_app, boolVarToBvarMap);
			LOG("pabs-debug", outs() << "ABS DEF: " << *abs_def << "\n";);

			Expr orig_def;
			if(isOpX<TRUE>(abs_def) || isOpX<FALSE>(abs_def))
			{
				orig_def = abs_def;
			}
			else
			{
				ExprMap abs_bvar_to_term_map;
				ExprVector abs_bvars;
				HornDbUtils::get_all_bvars(abs_def, std::back_inserter(abs_bvars));
				for(Expr abs_bvar : abs_bvars)
				{
					Expr term = (getRelToBoolToTermMap().find(orig_rel)->second).find(abs_bvar)->second;
					abs_bvar_to_term_map.insert(std::pair<Expr, Expr>(abs_bvar, term));
				}
				orig_def = replace(abs_def, abs_bvar_to_term_map);
			}
			LOG("pabs-debug", outs() << "ORIG DEF: " << *orig_def << "\n";);

			ExprVector orig_fapp_args;
			for(int i=0; i<bind::domainSz(orig_rel); i++)
			{
				Expr arg_i_type = bind::domainTy(orig_rel, i);
				Expr var = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", orig_rel->efac ())), arg_i_type));
				orig_fapp_args.push_back(var);
			}
			Expr orig_fapp = bind::fapp(orig_rel, orig_fapp_args);
			LOG("pabs-debug", outs() << "ORIG FAPP: " << *orig_fapp << "\n";);

			ExprVector bvars;
			HornDbUtils::get_all_bvars(orig_def, std::back_inserter(bvars));
			ExprMap bvarIdMap;
			for(Expr bvar : bvars)
			{
				int bvar_id = bind::bvarId(bvar);
				Expr bvar_type = bind::typeOf(bvar);
				Expr var = bind::fapp(bind::constDecl(variant::variant(bvar_id, mkTerm<std::string> ("V", bvar->efac ())), bvar_type));
				bvarIdMap.insert(std::pair<Expr, Expr>(bvar, var));
			}
			Expr orig_def_app = replace(orig_def, bvarIdMap);
			LOG("pabs-debug", outs() << "ORIG DEF APP: " << *orig_def_app << "\n";);
			out.addDef(orig_fapp, orig_def_app);
		}
		return true;
	}

	Expr HornDbUtils::applyArgsToBvars(Expr cand, Expr fapp, std::map<Expr, ExprVector> currentCandidates)
	{
	  ExprMap bvar_map = getBvarsToArgsMap(fapp, currentCandidates);
	  return replace(cand, bvar_map);
	}

	ExprMap HornDbUtils::getBvarsToArgsMap(Expr fapp, std::map<Expr, ExprVector> currentCandidates)
	{
	  Expr fdecl = bind::fname(fapp);
	  ExprVector terms = currentCandidates[fdecl];
	  Expr cand;
	  if(terms.size() == 1)
	  {
		  cand = currentCandidates[fdecl][0];
	  }
	  else if(terms.size() > 1)
	  {
		  cand = mknary<AND>(terms.begin(), terms.end());
	  }
	  else
	  {
		  errs() << "terms size wrong!\n";
		  assert(false);
	  }

	  ExprMap bvar_map;
	  ExprVector bvars;
	  HornDbUtils::get_all_bvars(cand, std::back_inserter(bvars));

	  for(ExprVector::iterator it = bvars.begin(); it != bvars.end(); ++it)
	  {
		  unsigned bvar_id = bind::bvarId(*it);
		  Expr app_arg = fapp->arg(bvar_id + 1);// To improve
		  bvar_map.insert(std::pair<Expr,Expr>(*it, app_arg));
	  }
	  return bvar_map;
	}

	Expr HornDbUtils::extractTransitionRelation(HornRule r, HornClauseDB &db)
	{
	  Expr ruleBody = r.body();
	  ExprMap body_map;
	  ExprVector body_pred_apps;
	  HornDbUtils::get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));

	  for(ExprVector::iterator itr = body_pred_apps.begin(); itr != body_pred_apps.end(); ++itr)
	  {
		  body_map.insert(std::pair<Expr, Expr>(*itr, mk<TRUE>((*itr)->efac())));
	  }

	  Expr body_constraints = replace(ruleBody, body_map);
	  return body_constraints;
	}

	bool HornDbUtils::hasBvarInRule(HornRule r, HornClauseDB &db, std::map<Expr, ExprVector> currentCandidates)
	{
		ExprVector pred_vector;
		HornDbUtils::get_all_pred_apps(r.body(), db, std::back_inserter(pred_vector));
		pred_vector.push_back(r.head());

		for (Expr pred : pred_vector)
		{
			ExprVector term_vec = currentCandidates.find(bind::fname(pred))->second;
			if(term_vec.size() > 1 || term_vec.size() == 1 && !isOpX<TRUE>(term_vec[0]))
			{
				return true;
			}
		}
		return false;
	}

	std::vector<std::string> HornDbUtils::split(std::string str,std::string pattern)
	{
		std::string::size_type pos;
		std::vector<std::string> result;
		str+=pattern;
		int size=str.size();

		for(int i=0; i<size; i++)
		{
			pos=str.find(pattern,i);
			if(pos<size)
			{
				std::string s=str.substr(i,pos-i);
				result.push_back(s);
				i=pos+pattern.size()-1;
			}
		}
		return result;
	}
}
