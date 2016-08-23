#ifndef HORNMODEL_CONVERTER__HH_
#define HORNMODEL_CONVERTER__HH_

#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornDbModel.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"

namespace seahorn
{
	class HornModelConverter
	{
	public:
		// converts a model from one database to another. returns false on failure.
		virtual bool convert (HornDbModel &in, HornDbModel &out) = 0;
	};

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

	class HornDbUtils
	{
	public:
		static Expr applyArgsToBvars(Expr cand, Expr fapp, std::map<Expr, ExprVector> currentCandidates);
		static ExprMap getBvarsToArgsMap(Expr fapp, std::map<Expr, ExprVector> currentCandidates);
		static Expr extractTransitionRelation(HornRule r, HornClauseDB &db);

		static std::vector<std::string> split(std::string str,std::string pattern);

		template<typename OutputIterator>
		static void get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out)
		{filter (e, IsPredApp(db), out);}

		template<typename OutputIterator>
		static void get_all_bvars (Expr e, OutputIterator out)
		{filter (e, IsBVar(), out);}

		template<typename OutputIterator>
		static void get_all_integers(Expr e, OutputIterator out)
		{filter (e, IsInteger(), out);}

		template<typename OutputIterator>
		static void get_all_booleans(Expr e, OutputIterator out)
		{filter (e, IsBoolean(), out);}

		static bool hasBvarInRule(HornRule r, HornClauseDB &db, std::map<Expr, ExprVector> currentCandidates);

		struct IsPredApp : public std::unary_function<Expr, bool>
		{
			 HornClauseDB &m_db;
			 IsPredApp (HornClauseDB &db) : m_db (db) {}

			 bool operator() (Expr e)
			 {return bind::isFapp (e) && m_db.hasRelation (bind::fname(e));}
		};

		struct IsBVar : public std::unary_function<Expr, bool>
		{
			 IsBVar () {}
			 bool operator() (Expr e)
			 {return bind::isBVar (e);}
		};

		struct IsInteger : public std::unary_function<Expr, bool>
		{
			IsInteger() {}
			bool operator() (Expr e)
			{return bind::isIntConst (e);}
		};

		struct IsBoolean : public std::unary_function<Expr, bool>
		{
			IsBoolean() {}
			bool operator() (Expr e)
			{return bind::isBoolConst (e);}
		};
	};
}

#endif
