#include "seahorn/HornDbModel.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDB.hh"

#include "ufo/Expr.hpp"
#include <vector>

#include "ufo/Stats.hh"

namespace seahorn
{
	void HornDbModel::addDef(Expr fapp, Expr lemma)
	{
		if (isOpX<TRUE> (lemma) || isOpX<FALSE> (lemma))
		{
			relToDefMap.insert(std::pair<Expr, Expr>(bind::fname(fapp), lemma));
			return;
		}

		assert (bind::isFapp (fapp));

		ExprMap actual_arg_to_bvar_map;

		for(int i=0; i<bind::domainSz(bind::fname(fapp)); i++)
		{
			Expr arg_i = fapp->arg(i+1);
			Expr bvar_i = bind::bvar(i, bind::typeOf(arg_i));
			actual_arg_to_bvar_map.insert(std::pair<Expr, Expr>(arg_i, bvar_i));
		}

		Expr lemma_def = replace(lemma, actual_arg_to_bvar_map);

		relToDefMap.insert(std::pair<Expr, Expr>(bind::fname(fapp), lemma_def));
	}

	Expr HornDbModel::getDef(Expr fapp)
	{
		Expr rel = bind::fname(fapp);
		Expr lemma_def = relToDefMap.find(rel)->second;

		ExprMap bvar_to_actual_arg_map;

		for(int i=0; i<bind::domainSz(bind::fname(fapp)); i++)
		{
			Expr arg_i = fapp->arg(i+1);
			Expr bvar_i = bind::bvar(i, bind::typeOf(arg_i));
			bvar_to_actual_arg_map.insert(std::pair<Expr, Expr>(bvar_i, arg_i));
		}

		Expr lemma = replace(lemma_def, bvar_to_actual_arg_map);
		return lemma;
	}
}
