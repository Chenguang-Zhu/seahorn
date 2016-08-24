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

	class PredAbsHornModelConverter : public HornModelConverter
	{
	private:
		std::map<Expr, ExprMap> relToBoolToTermMap;
		std::map<Expr, Expr> newToOldPredMap;
		HornClauseDB* abs_db;

		std::map<Expr, ExprMap>& getRelToBoolToTermMap() {return relToBoolToTermMap;}
	public:
		PredAbsHornModelConverter() {}
		virtual ~PredAbsHornModelConverter() {}
		bool convert (HornDbModel &in, HornDbModel &out);

		void addRelToBoolToTerm(Expr rel, ExprMap &boolToTermMap) {relToBoolToTermMap.insert(std::pair<Expr, ExprMap>(rel, boolToTermMap));}
		void setNewToOldPredMap(std::map<Expr, Expr> &newToOldMap) {newToOldPredMap = newToOldMap;}
		void setAbsDB(HornClauseDB &db) {abs_db = &db;}
	};

	class PredicateAbstractionAnalysis
	{
	private:
	    std::map<Expr, Expr> oldToNewPredMap;
	    std::map<Expr, Expr> newToOldPredMap;
	    std::map<Expr, ExprVector> currentCandidates;

	    HornifyModule& m_hm;

	public:
	    PredicateAbstractionAnalysis(HornifyModule &hm) : m_hm(hm) {}
	    ~PredicateAbstractionAnalysis() {}

		void guessCandidate(HornClauseDB &db);
		ExprVector relToCand(Expr fdecl);
		HornClauseDB generateAbstractDB(HornClauseDB &db, PredAbsHornModelConverter &converter);
		void generateAbstractRelations(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter);
		void generateAbstractRules(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter);
		void generateAbstractQueries(HornClauseDB &db, HornClauseDB &new_DB);

		ExprVector applyTemplatesFromExperimentFile(Expr fdecl, std::string filepath);
		void parseLemmasFromExpFile(Expr bvar, ExprVector& lemmas, std::string filepath);
	};

	class PredicateAbstraction : public llvm::ModulePass
	{
	public:
	    static char ID;

	    PredicateAbstraction() : ModulePass(ID) {}
	    virtual ~PredicateAbstraction() {}
	    void releaseMemory () {m_fp.reset (nullptr);}
	    virtual bool runOnModule (Module &M);
	    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
	    virtual const char* getPassName () const {return "PredicateAbstraction";}

	    ufo::ZFixedPoint<ufo::EZ3>& getZFixedPoint () {return *m_fp;}

	    void printInvars(Function &F, HornDbModel &origModel);
	    void printInvars(Module &M, HornDbModel &origModel);
	private:
	    std::unique_ptr<ufo::ZFixedPoint <ufo::EZ3> >  m_fp;
	};
}

#endif
