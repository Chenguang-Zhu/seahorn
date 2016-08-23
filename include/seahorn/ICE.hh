#ifndef ICE__HH_
#define ICE__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/HornClauseDBWto.hh"

namespace seahorn
{
  using namespace llvm;

  class ICE : public llvm::ModulePass
  {
  public:
    static char ID;

    ICE() : ModulePass(ID) {}
    virtual ~ICE() {}

    virtual bool runOnModule (Module &M);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "ICE";}
  };

  class ICE_GuessCandidates
  {
  public:
	  static std::map<Expr, Expr> guessCandidates(HornClauseDB &db);
	  //Simple templates
	  static Expr relToCand(Expr pred);
	  static Expr C5RelToCand(Expr pred);
	  //Functions for generating complex invariants
	  static Expr applyComplexTemplates(Expr fdecl);
	  static void generateLemmasForOneBvar(Expr bvar, ExprVector &conjuncts);
  };

  class ICEHoudini
  {
  public:
	  ICEHoudini(HornifyModule &hm) : m_hm(hm)  {}
	  virtual ~ICEHoudini() {}
  private:
	  HornifyModule &m_hm;
      std::map<Expr,Expr> currentCandidates;

    public:
      HornifyModule& getHornifyModule() {return m_hm;}
      std::map<Expr,Expr>& getCurrentCandidates() {return currentCandidates;}
      void setInitialCandidatesSet(std::map<Expr, Expr> candidates) {currentCandidates = candidates;}

    public:
      void runICEHoudini(int config);

      //Utility Functions
      Expr fAppToCandApp(Expr fapp);
      Expr applyArgsToBvars(Expr cand, Expr fapp);
      ExprMap getBvarsToArgsMap(Expr fapp);

      Expr extractTransitionRelation(HornRule r, HornClauseDB &db);

      template<typename OutputIterator>
  	  void get_all_bvars (Expr e, OutputIterator out);

  	  template<typename OutputIterator>
  	  void get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out);

      //Functions for generating Positive Examples
      void generatePositiveWitness(std::map<Expr, ExprVector> &relationToPositiveStateMap);
      void getReachableStates(std::map<Expr, ExprVector> &relationToPositiveStateMap, Expr from_pred, Expr from_pred_state);
      void getRuleHeadState(std::map<Expr, ExprVector> &relationToPositiveStateMap, HornRule r, Expr from_pred_state);

      //Add Houdini invs to default solver
      void addInvarCandsToProgramSolver();
  };

  class ICEHoudiniContext
  {
  protected:
	  ICEHoudini &m_houdini;
	  HornClauseDBWto &m_db_wto;
	  std::list<HornRule> &m_workList;
  public:
	  ICEHoudiniContext(ICEHoudini& houdini, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
		  m_houdini(houdini), m_db_wto(db_wto), m_workList(workList) {}
	  virtual void run() = 0;
	  virtual bool validateRule(HornRule r, ZSolver<EZ3> &solver) = 0;
	  void weakenRuleHeadCand(HornRule r, ZModel<EZ3> m);
	  void addUsedRulesBackToWorkList(HornClauseDBWto &db_wto, std::list<HornRule> &workList, HornRule r);
  };

  class ICEHoudini_Naive : public ICEHoudiniContext
  {
  private:
	  ZSolver<EZ3> m_solver;
  public:
	  ICEHoudini_Naive(ICEHoudini& houdini, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
		  ICEHoudiniContext(houdini, db_wto, workList), m_solver(houdini.getHornifyModule().getZContext()) {}
	  void run();
	  bool validateRule(HornRule r, ZSolver<EZ3> &solver);
  };

  class ICEHoudini_Each_Solver_Per_Rule : public ICEHoudiniContext
  {
  private:
  	  std::map<HornRule, ZSolver<EZ3>> m_ruleToSolverMap;
  public:
  	  ICEHoudini_Each_Solver_Per_Rule(ICEHoudini& houdini, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
  		  ICEHoudiniContext(houdini, db_wto, workList), m_ruleToSolverMap(assignEachRuleASolver()){}
  	  void run();
  	  bool validateRule(HornRule r, ZSolver<EZ3> &solver);
  	  std::map<HornRule, ZSolver<EZ3>> assignEachRuleASolver();
  };

  class ICEHoudini_Each_Solver_Per_Relation : public ICEHoudiniContext
  {
  private:
	  std::map<Expr, ZSolver<EZ3>> m_relationToSolverMap;
  public:
	  ICEHoudini_Each_Solver_Per_Relation(ICEHoudini& houdini, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
		  ICEHoudiniContext(houdini, db_wto, workList), m_relationToSolverMap(assignEachRelationASolver()){}
	  void run();
	  bool validateRule(HornRule r, ZSolver<EZ3> &solver);
	  std::map<Expr, ZSolver<EZ3>> assignEachRelationASolver();
  };
}

#endif /* HOUDNINI__HH_ */
