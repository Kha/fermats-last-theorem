module

public import Definitions.Def_ModularCurve_AtkinLehner
public import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
public import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_ord_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N) :
    (cuspInftyBar N).ord f = (f : LaurentSeries (AlgebraicClosure ℚ)).order :=
  ModularCurve.ord_qInftyPlaceBar (AlgebraicClosure ℚ) _ f
