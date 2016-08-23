#ifndef PREDICATE_ABSTRACTION__HH_
#define PREDICATE_ABSTRACTION__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornDbModel.hh"
#include "seahorn/HornModelConverter.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/HornClauseDBWto.hh"

namespace seahorn
{
	using namespace llvm;

	class PredicateAbstractionAnalysis
	{
	private:
	    std::map<Expr, Expr> oldToNewPredMap;
	    std::map<Expr, Expr> newToOldPredMap;
	    std::map<Expr, ExprVector> currentCandidates;

	    std::unique_ptr<ufo::ZFixedPoint <ufo::EZ3> >  m_fp;
	    HornifyModule& m_hm;

	    void initAbsModelFromFP(HornDbModel &absModel, HornClauseDB &db, ZFixedPoint<EZ3> &fp);

	public:
	    PredicateAbstractionAnalysis(HornifyModule &hm) : m_hm(hm) {}
	    ~PredicateAbstractionAnalysis() {m_fp.reset (nullptr);}

	    ufo::ZFixedPoint<ufo::EZ3>& getZFixedPoint () {return *m_fp;}

	    void runAnalysis();
		void guessCandidate(HornClauseDB &db);
		ExprVector relToCand(Expr fdecl);
		HornClauseDB generateAbstractDB(HornClauseDB &db, PredAbsHornModelConverter &converter);
		void generateAbstractRelations(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter);
		void generateAbstractRules(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter);
		void generateAbstractQueries(HornClauseDB &db, HornClauseDB &new_DB);
		void printInvars(HornClauseDB &db, HornDbModel &origModel);

		ExprVector applyTemplatesFromExperimentFile(Expr fdecl, std::string filepath);
		void parseLemmasFromExpFile(Expr bvar, ExprVector& lemmas, std::string filepath);
	};

	class PredicateAbstraction : public llvm::ModulePass
	{
	public:
	    static char ID;

	    PredicateAbstraction() : ModulePass(ID) {}
	    virtual ~PredicateAbstraction() {}
	    virtual bool runOnModule (Module &M);
	    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
	    virtual const char* getPassName () const {return "PredicateAbstraction";}
	};
}

#endif
