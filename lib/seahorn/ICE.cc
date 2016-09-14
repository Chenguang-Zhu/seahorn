#include "seahorn/ICE.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/GuessCandidates.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include <vector>
#include <boost/logic/tribool.hpp>
#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/json_parser.hpp>
#include "seahorn/HornClauseDBWto.hh"
#include <algorithm>

#include "ufo/Stats.hh"

#include <iostream>
#include <string>

#include <stdlib.h>
#include <stdio.h>

using namespace llvm;

namespace seahorn
{
  #define SAT_OR_INDETERMIN true
  #define UNSAT false

  #define NAIVE 0
  #define EACH_RULE_A_SOLVER 1
  #define EACH_RELATION_A_SOLVER 2

  /*ICEPass methods begin*/

  char ICEPass::ID = 0;

  bool ICEPass::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();

    //Use commandline option to replace it.
    int config = NAIVE;

    Stats::resume ("ICE inv");
    ICE ice(hm);
    ice.setupC5();
    ice.genInitialCandidates(hm.getHornClauseDB());
    ice.runICE(config);
    Stats::stop ("ICE inv");

    return false;
  }

  void ICEPass::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll();
  }

  /*ICEPass methods end*/

  /*ICE methods begin*/

  void ICE::addInvarCandsToProgramSolver()
  {
	  auto &db = m_hm.getHornClauseDB();
	  for(Expr rel : db.getRelations())
	  {
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::bvar(i, arg_i_type));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);
		  Expr cand_app = m_candidate_model.getDef(fapp);
		  LOG("candidates", errs() << "HEAD: " << *fapp << "\n";);
		  LOG("candidates", errs() << "CAND: " << *cand_app << "\n";);
		  if(!isOpX<TRUE>(cand_app))
		  {
			  LOG("candidates", errs() << "ADD CONSTRAINT\n";);
			  db.addConstraint(fapp, cand_app);
		  }
	  }
//	  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
//	  {
//			HornRule r = *it;
//			Expr rhead_app = r.head();
//			Expr rhead_cand_app = m_candidate_model.getDef(rhead_app);
//			LOG("candidates", errs() << "HEAD: " << *rhead_app << "\n";);
//			LOG("candidates", errs() << "CAND: " << *rhead_cand_app << "\n";);
//			if(!isOpX<TRUE>(rhead_cand_app))
//			{
//				LOG("candidates", errs() << "ADD CONSTRAINT\n";);
//				db.addConstraint(rhead_app, rhead_cand_app);
//			}
//	  }
  }

  //Set .names file and .interval file
  void ICE::setupC5()
  {
	  m_C5filename = "FromCmd";

	  std::ofstream names_of(m_C5filename + ".names");
	  if(!names_of)return;

	  std::ofstream intervals_of(m_C5filename + ".intervals");
	  if(!intervals_of)return;

	  int lowerInterval = 2;
	  int upperInterval = 2;

	  //convert predicate names to the name format of C5
	  auto &db = m_hm.getHornClauseDB();
	  int rel_index = 0;
	  for(Expr rel : db.getRelations())
	  {
		  Expr C5_rel_name = variant::variant(rel_index, mkTerm<std::string>(std::string("PRED"), rel->efac()));
		  m_rel_to_c5_rel_name_map.insert(std::make_pair(rel, C5_rel_name));
		  m_c5_rel_name_to_rel_map.insert(std::make_pair(C5_rel_name, rel));
		  rel_index ++;
	  }

	  names_of << "invariant.\n";

	  //first attribute is the predicate names
	  names_of << "$pc: ";
	  int counter=0;
	  for(Expr rel : db.getRelations())
	  {
		  Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(rel)->second;
		  if(counter == db.getRelations().size()-1)
		  {
			  names_of << *C5_rel_name << ".\n";
		  }
		  else
		  {
			  names_of << *C5_rel_name << ",";
		  }
		  counter++;
	  }

	  //each argument of each predicate is an attribute
	  for(Expr rel : db.getRelations())
	  {
		  Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(rel)->second;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  if(isOpX<INT_TY>(bind::domainTy(rel, i)) || isOpX<BOOL_TY>(bind::domainTy(rel, i)))
			  {
				  Expr bvar_i = bind::bvar(i, bind::domainTy(rel, i));
				  Expr arg_i = bind::fapp(bvar_i);
				  Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
				  m_attr_name_to_expr_map.insert(std::make_pair(attr_name_i, arg_i));
				  names_of << attr_name_i << ": continuous.\n";
				  upperInterval ++;
			  }
			  else
			  {
				  outs() << "NOT INT OR BOOL TYPE!\n";
			  }
		  }
		  std::string interval_line = boost::lexical_cast<std::string>(lowerInterval) + " " + boost::lexical_cast<std::string>(upperInterval-1) + "\n";
		  intervals_of << interval_line;
		  lowerInterval = upperInterval;
		  upperInterval = lowerInterval;
	  }
      names_of << "invariant: true, false.\n";
	  names_of.close();
	  intervals_of.close();
  }

  void ICE::genInitialCandidates(HornClauseDB &db)
  {
	  for(Expr rel : db.getRelations())
	  {
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr bvar_i = bind::bvar(i, arg_i_type);
			  Expr arg_i = bind::fapp(bvar_i);
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);
		  Expr True = mk<TRUE>(rel->efac());

		  outs() << *fapp << "\n";
		  m_candidate_model.addDef(fapp, True);
	  }
  }

  void ICE::C5learn()
  {
	  generateC5DataAndImplicationFiles();

	  //system("/home/chenguang/Desktop/C50-ICE/C50/c5.0.dt_penalty -I 1 -m 1 -f " + m_C5filename);
	  FILE *fp;
	  FILE *wp;
	  wp = fopen("C5_temp","w+");
	  std::string command = "/home/chenguang/Desktop/C50-ICE/C50/c5.0.dt_penalty -I 1 -m 1 -f " + m_C5filename;
	  std::string access = "r";
	  if((fp = popen(command.c_str(), access.c_str())) == NULL)
	  {
		  perror("popen failed!\n");
		  return;
	  }
	  char buf[1024];

	  size_t status = fread(buf, sizeof(char), sizeof(buf), fp);
	  if(status == 0)
	  {
		  outs() << "read from popen failed!\n";
		  return;
	  }
	  fwrite(buf, 1, sizeof(buf), wp);

	  pclose(fp);
	  fclose(wp);

	  //parse the .json file to ptree
	  std::ifstream if_json(m_C5filename + ".json");
	  std::ostringstream json_buf;

	  char ch;
	  while(json_buf && if_json.get(ch))
	  { json_buf.put(ch); }

	  std::string json_string =  json_buf.str();

	  boost::property_tree::ptree pt;
	  std::stringstream ss(json_string);
	  try
	  { boost::property_tree::json_parser::read_json(ss, pt); }
	  catch(boost::property_tree::ptree_error & e)
	  { outs() << "READ JSON ERROR!\n"; return; }

	  //parse ptree to invariant format???

	  auto &db = m_hm.getHornClauseDB();
	  for(Expr rel : db.getRelations())
	  {
		  convertPtreeToInvCandidate(pt, rel);
	  }

  }

  void ICE::convertPtreeToInvCandidate(boost::property_tree::ptree pt, Expr rel)
  {
	  Expr rel_name = bind::fname(rel);
	  std::ostringstream oss;
	  oss << rel_name;
	  boost::property_tree::ptree sub_pt = pt.get_child(oss.str());
	  std::list<Expr> stack;
	  stack.push_back(mk<TRUE>(rel_name->efac()));
	  std::list<std::list<Expr>> final_formula = constructFormula(stack, sub_pt);
	  ExprVector disjunctions;
	  for(std::list<std::list<Expr>>::iterator disj_it = final_formula.begin(); disj_it != final_formula.end(); ++disj_it)
	  {
		  ExprVector conjunctions;
		  for(std::list<Expr>::iterator conj_it = (*disj_it).begin(); conj_it != (*disj_it).end(); ++conj_it)
		  {
			  conjunctions.push_back(*conj_it);
		  }
		  Expr disjunct = mknary<AND>(conjunctions.begin(), conjunctions.end());
		  disjunctions.push_back(disjunct);
	  }
	  Expr candidate = mknary<OR>(disjunctions.begin(), disjunctions.end());

	  ExprVector arg_list;
	  for(int i=0; i<bind::domainSz(rel); i++)
	  {
		  Expr arg_i_type = bind::domainTy(rel, i);
		  Expr bvar_i = bind::bvar(i, arg_i_type);
		  Expr arg_i = bind::fapp(bvar_i);
		  arg_list.push_back(arg_i);
	  }
	  Expr fapp = bind::fapp(rel, arg_list);

	  m_candidate_model.addDef(fapp, candidate);
  }

  std::list<std::list<Expr>> ICE::constructFormula(std::list<Expr> stack, boost::property_tree::ptree sub_pt)
  {
	  Expr decision_expr;
	  std::list<std::list<Expr>> final_formula;
	  //leaf node
	  if(sub_pt.size() == 0)
	  {
		  if(sub_pt.get<std::string>("classification") == "true" || sub_pt.get<std::string>("classification") == "True")
		  {
			 std::list<Expr> new_conjunct = stack;
			 final_formula.push_back(new_conjunct);
			 return final_formula;
		  }
		  else if(sub_pt.get<std::string>("classification") == "false" || sub_pt.get<std::string>("classification") == "False")
		  {
			 return final_formula;
		  }
	  }
	  //internal node
	  else
	  {
		  std::string attr_name = sub_pt.get<std::string>("attribute");
		  ExprMap::iterator it = m_attr_name_to_expr_map.find(mkTerm<std::string>(attr_name, decision_expr->efac()));
		  assert(it != m_attr_name_to_expr_map.end());
		  Expr attr_expr = it->second;

		  if(bind::isBoolVar(attr_expr))
		  {
			 decision_expr = mk<NEG>(attr_expr);
			 int cut = sub_pt.get<int>("cut");
			 assert(cut == 0);
		  }
		  else if(bind::isIntVar(attr_expr))
		  {
			 int cut = sub_pt.get<int>("cut");
			 Expr threshold = mkTerm<mpz_class>(cut, attr_expr->efac());
			 decision_expr = mk<LT>(attr_expr, threshold);
		  }
		  else
		  {
			 outs() << "DECISION NODE TYPE WRONG!\n";
			 return final_formula;
		  }
		  stack.push_back(decision_expr);
		  assert(sub_pt.children().size() == 2);
		  boost::property_tree::ptree::assoc_iterator child_itr = sub_pt.ordered_begin();
		  std::list<std::list<Expr>> final_formula_left = constructFormula(stack, child_itr->second);
		  stack.pop_back();
		  stack.push_back(mk<NEG>(decision_expr));
		  std::list<std::list<Expr>> final_formula_right = constructFormula(stack, (++child_itr)->second);
		  stack.pop_back();
		  final_formula_left.insert(final_formula_left.end(), final_formula_right.begin(), final_formula_right.end());
		  return final_formula_left;
	  }
	  return final_formula;
  }

  void ICE::generateC5DataAndImplicationFiles()
  {
	  //generate .data file
	  std::ofstream data_of(m_C5filename + ".data");
	  if(!data_of)return;

	  auto &db = m_hm.getHornClauseDB();

	  for(DataPoint pos_dp : m_pos_data_set)
	  {
		  data_of << pos_dp.getPredName();
		  for(Expr attr : pos_dp.getAttrValues())
		  {
			  data_of << "," << *attr;
		  }
		  data_of << "true\n";
	  }

	  for(DataPoint neg_dp : m_neg_data_set)
	  {
		  data_of << neg_dp.getPredName();
		  for(Expr attr : neg_dp.getAttrValues())
		  {
			  data_of << "," << *attr;
		  }
		  data_of << "false\n";
	  }

	  for(DataPoint impl_dp : m_impl_cex_set)
	  {
		  if(m_pos_data_set.count(impl_dp) != 0 || m_neg_data_set.count(impl_dp) != 0)
		  {
			  continue;
		  }
		  data_of << impl_dp.getPredName();
		  for(Expr attr : impl_dp.getAttrValues())
		  {
			  data_of << "," << *attr;
		  }
		  data_of << "?\n";
	  }

	  data_of.close();

	  //generate .implications file
	  std::ofstream implications_of(m_C5filename + ".implications");
	  if(!implications_of)return;

	  for(std::pair<DataPoint, DataPoint> impl_pair : m_impl_pair_set)
	  {
		  DataPoint start_point = impl_pair.first;
		  std::map<DataPoint, int>::iterator it = m_data_point_to_index_map.find(start_point);
		  assert(it != m_data_point_to_index_map.end());
		  int start_index = it->second;

		  DataPoint end_point = impl_pair.second;
		  std::map<DataPoint, int>::iterator itr = m_data_point_to_index_map.find(end_point);
		  assert(itr != m_data_point_to_index_map.end());
		  int end_index = itr->second;

		  implications_of << start_index << " " << end_index << "\n";
	  }

	  implications_of.close();
  }

  /*
   * Main loop of ICE algorithm
   */
  void ICE::runICE(int config)
  {
	  //load the Horn clause database
	  auto &db = m_hm.getHornClauseDB ();
	  db.buildIndexes ();

	  //construct the new horn clause DB, with pos and neg new rules.
	  HornClauseDB new_db(db.getExprFactory());
	  constructNewDB(db, new_db);
	  outs() << "NEW DB:\n" << new_db;

	  //build the new DB wto
	  HornClauseDBCallGraph callgraph(new_db);
	  HornClauseDBWto new_db_wto(callgraph);
	  new_db_wto.buildWto();

	  std::list<HornRule> workList;
	  workList.insert(workList.end(), new_db.getRules().begin(), new_db.getRules().end());
	  workList.reverse();

	  if (config == NAIVE)
	  {
		  ICE_Naive ice_naive(*this, new_db_wto, workList);
		  ice_naive.run();
	  }

	  addInvarCandsToProgramSolver();
  }

  void ICE::constructNewDB(HornClauseDB &db, HornClauseDB &new_db)
  {
	  //copy old db contents to new db
	  for(Expr rel : db.getRelations())
	  {
		  new_db.registerRelation(rel);
	  }
	  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
	  {
		  HornRule r = *it;
		  new_db.addRule(r);
	  }
	  for(auto query : db.getQueries())
	  {
		  new_db.addQuery(query);
	  }
	  addPosNegRulesToDB(db, new_db);
  }

  void ICE::addPosNegRulesToDB(HornClauseDB &db, HornClauseDB &new_db)
  {
	  //Extract verifier.error
	  Expr error_pred;
	  for(Expr rel : db.getRelations())
	  {
		  std::ostringstream oss;
		  oss << bind::fname(rel);
		  if(oss.str() == "verifier.error") //how to identify error predicate?
		  {
			 error_pred = bind::fname(rel);
		  }
	  }
	  outs() << "ERROR PRED: " << *error_pred << "\n";
	  //Add Pos and Neg Rules
	  for(Expr rel : db.getRelations())
	  {
		  ExprVector args;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i = bind::bvar(i, bind::domainTy(rel, i));
			  Expr arg_i_app = bind::fapp(arg_i);
			  args.push_back(arg_i_app);
		  }
		  Expr rel_app = bind::fapp(rel, args);
		  Expr cand_app = m_candidate_model.getDef(rel_app);

		  //pos
		  Expr new_pos_head = bind::fapp(error_pred);
		  Expr new_pos_body = mk<AND>(rel_app, mk<NEG>(cand_app));
		  HornRule new_pos_rule(args, new_pos_head, new_pos_body);
		  new_db.addRule(new_pos_rule);
		  m_pos_rule_set.insert(new_pos_rule);

		  //neg
		  Expr new_neg_head = rel_app;
		  Expr new_neg_body = cand_app;
		  HornRule new_neg_rule(args, new_neg_head, new_neg_body);
		  new_db.addRule(new_neg_rule);
		  m_neg_rule_set.insert(new_neg_rule);
	  }
  }

  void ICE_Naive::run()
  {
	  int index = 0;
  	  while(!m_workList.empty())
  	  {
  		  LOG("ice", errs() << "WORKLIST SIZE: " << m_workList.size() << "\n";);
  		  HornRule r = m_workList.front();
  		  m_workList.pop_front();
  		  LOG("ice", errs() << "RULE HEAD: " << *(r.head()) << "\n";);
  		  LOG("ice", errs() << "RULE BODY: " << *(r.body()) << "\n";);
  		  if (validateRule(r, m_solver) != UNSAT)
  		  {
  			  addUsedRulesBackToWorkList(m_db_wto, m_workList, r); //including itself
  			  ZModel<EZ3> m = m_solver.getModel();

  			  //if pos rule
			  if(m_ice.getPosRuleSet().count(r) != 0)
			  {
				  outs() << "POS RULE:\n";
				  std::list<Expr> attr_values;

				  ExprVector body_preds;
				  get_all_pred_apps(r.body(), m_ice.getHornifyModule().getHornClauseDB(), std::back_inserter(body_preds));
				  Expr pred = body_preds[0];
				  for(int i=0; i<bind::domainSz(bind::fname(pred)); i++)
				  {
					  Expr arg_i = pred->arg(i+1);
					  Expr arg_i_value = m.eval(arg_i);
					  attr_values.push_back(arg_i_value);
				  }

				  DataPoint pos_dp(bind::fname(bind::fname(r.head())), attr_values);
				  m_ice.addPosCex(pos_dp);
				  m_ice.addDataPointToIndex(pos_dp, index);
				  index++;
			  }
			  //if neg rule
			  else if(m_ice.getNegRuleSet().count(r) != 0)
			  {
				  outs() << "NEG RULE:\n";
				  std::list<Expr> attr_values;
				  Expr head = r.head();
				  for(int i=0; i<bind::domainSz(bind::fname(head)); i++)
				  {
					  Expr arg_i = head->arg(i+1);
					  Expr arg_i_value = m.eval(arg_i);
					  attr_values.push_back(arg_i_value);
				  }

				  DataPoint neg_dp(bind::fname(bind::fname(head)), attr_values);
				  m_ice.addNegCex(neg_dp);
				  m_ice.addDataPointToIndex(neg_dp, index);
				  index++;
			  }
			  else //if impl rule
			  {
//				  ExprVector body_preds;
//				  get_all_pred_apps(r.body(), m_ice.getHornifyModule().getHornClauseDB(), body_preds);
//				  if(body_preds.size() != 1)
//				  {
//					  continue;
//				  }
//				  Expr head = r.head();

				  outs() << "IMPL RULE:\n";
				  std::list<Expr> start_attr_values;
				  Expr head = r.head();
				  ExprVector body_preds;
				  get_all_pred_apps(r.body(), m_ice.getHornifyModule().getHornClauseDB(), std::back_inserter(body_preds));
				  Expr body_pred = body_preds[0];
				  for(int i=0; i<bind::domainSz(bind::fname(body_pred)); i++)
				  {
					  Expr arg_i = body_pred->arg(i+1);
					  Expr arg_i_value = m.eval(arg_i);
					  start_attr_values.push_back(arg_i_value);
				  }
				  DataPoint start_point(bind::fname(bind::fname(body_pred)), start_attr_values);

				  std::list<Expr> end_attr_values;
				  for(int i=0; i<bind::domainSz(bind::fname(head)); i++)
				  {
					  Expr arg_i = head->arg(i+1);
					  Expr arg_i_value = m.eval(arg_i);
					  end_attr_values.push_back(arg_i_value);
				  }
				  DataPoint end_point(bind::fname(bind::fname(head)), end_attr_values);

				  m_ice.addImplCex(start_point);
				  m_ice.addDataPointToIndex(start_point, index);
				  index++;
				  m_ice.addImplCex(end_point);
				  m_ice.addDataPointToIndex(end_point, index);
				  index++;
				  m_ice.addImplPair(std::make_pair(start_point, end_point));
			  }
  			  m_ice.C5learn(); //update candidate model inside
  		  }
  		  else
  		  {
  			  //UNSAT, we are good. Go to next rule.
  		  }
  	  }
  }

  bool ICE_Naive::validateRule(HornRule r, ZSolver<EZ3> &solver)
  {
	  solver.reset();

	  auto &m_hm = m_ice.getHornifyModule();
	  auto &db = m_hm.getHornClauseDB();

	  Expr ruleHead_cand_app = m_ice.getCandidateModel().getDef(r.head());
	  Expr neg_ruleHead_cand_app = mk<NEG>(ruleHead_cand_app);
	  solver.assertExpr(neg_ruleHead_cand_app);

	  Expr ruleBody = r.body();
	  ExprVector body_pred_apps;
	  get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));
	  for(Expr body_app : body_pred_apps)
	  {
		  solver.assertExpr(m_ice.getCandidateModel().getDef(body_app)); //add each body predicate app
	  }

	  solver.assertExpr(extractTransitionRelation(r, db));

	  solver.toSmtLib(errs());
	  boost::tribool isSat = solver.solve();
	  if(isSat)
	  {
		  LOG("ice", errs() << "SAT\n";);
		  return SAT_OR_INDETERMIN;
	  }
	  else if(!isSat)
	  {
		  LOG("ice", errs() << "UNSAT\n";);
		  return UNSAT;
	  }
	  else //if indeterminate
	  {
		  LOG("ice", errs() << "INDETERMINATE\n";);
		  return SAT_OR_INDETERMIN;
	  }
  }

  /*
   * Given a rule, weaken its head's candidate
   */
  void ICEContext::weakenRuleHeadCand(HornRule r, ZModel<EZ3> m)
  {
	  Expr ruleHead_app = r.head();
	  Expr ruleHead_cand_app = m_ice.getCandidateModel().getDef(ruleHead_app);

	  LOG("ice", errs() << "HEAD CAND APP: " << *ruleHead_cand_app << "\n";);

	  if(isOpX<TRUE>(ruleHead_cand_app))
	  {
			return;
	  }
	  if(!isOpX<AND>(ruleHead_cand_app))
	  {
			Expr weaken_cand = mk<TRUE>(ruleHead_cand_app->efac());
			m_ice.getCandidateModel().addDef(ruleHead_app, weaken_cand);
	  }
	  else
	  {
			ExprVector head_cand_args;
			head_cand_args.insert(head_cand_args.end(), ruleHead_cand_app->args_begin(), ruleHead_cand_app->args_end());
			int num_of_lemmas = head_cand_args.size();

			for(ExprVector::iterator it = head_cand_args.begin(); it != head_cand_args.end(); ++it)
			{
				LOG("ice", errs() << "EVAL: " << *(m.eval(*it)) << "\n";);
				if(isOpX<FALSE>(m.eval(*it)))
				{
					head_cand_args.erase(it);
					break;
				}
			}

			// This condition can be reached only when the solver answers Indeterminate
			// In this case, we remove an arbitrary lemma (the first one)
			if(head_cand_args.size() == num_of_lemmas)
			{
				LOG("ice", errs() << "INDETERMINATE REACHED" << "\n");
				head_cand_args.erase(head_cand_args.begin());
			}

			ExprMap bvarToArgMap;
			for(int i=0; i<bind::domainSz(bind::fname(ruleHead_app)); i++)
			{
				Expr arg_i = ruleHead_app->arg(i+1);
				Expr bvar_i = bind::bvar(i, bind::typeOf(arg_i));
				bvarToArgMap.insert(std::make_pair(bvar_i, arg_i));
			}

			if(head_cand_args.size() > 1)
			{
				Expr weaken_cand = mknary<AND>(head_cand_args.begin(), head_cand_args.end());
				Expr weaken_cand_app = replace(weaken_cand, bvarToArgMap);
				m_ice.getCandidateModel().addDef(ruleHead_app, weaken_cand_app);
			}
			else
			{
				Expr weaken_cand = head_cand_args[0];
				Expr weaken_cand_app = replace(weaken_cand, bvarToArgMap);
				m_ice.getCandidateModel().addDef(ruleHead_app, weaken_cand_app);
			}
	  }
	  LOG("ice", errs() << "HEAD AFTER WEAKEN: " << *(m_ice.getCandidateModel().getDef(ruleHead_app)) << "\n";);
  }

  /*
   * Given a rule head, extract all rules using it in body, then add all such rules to the end of workList
   */
  void ICEContext::addUsedRulesBackToWorkList(HornClauseDBWto &db_wto, std::list<HornRule> &workList, HornRule r)
  {
	  auto &m_hm = m_ice.getHornifyModule();
	  auto &db = m_hm.getHornClauseDB();
  	  Expr ruleHead_app = r.head();
  	  Expr ruleHead_rel = bind::fname(ruleHead_app);

  	  for(Expr fdecl : boost::make_iterator_range(db_wto.heads_begin(ruleHead_rel), db_wto.heads_end(ruleHead_rel)))
  	  {
  		  //LOG("ice", errs() << "[USEFUL PRED]: " << *fdecl << "\n";);
  		  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it!=db.getRules().end(); ++it)
  		  {
  			  if(*it == r)
  			  {
  				  continue;
  			  }
  			  if(bind::fname((*it).head()) == fdecl)
  			  {
  				  LOG("ice", errs() << "[NEED RULE]: " << *((*it).head()) << " <===== " << *((*it).body()) << "\n";);
  				  if(std::find(workList.begin(), workList.end(), *it) == workList.end())
  				  {
  					  workList.push_back(*it);
  				  }
  			  }
  		  }
  	  }
  	  workList.push_back(r); //including the sat rule itself.
  }

}