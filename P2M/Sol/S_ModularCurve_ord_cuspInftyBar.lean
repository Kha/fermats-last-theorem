module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Sol.S_ModularCurve_ord_qInftyPlaceBar
import P2M.Util

namespace P2MW.S_ModularCurve_ord_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N) :
    (cuspInftyBar N).ord f = (f : LaurentSeries (AlgebraicClosure ℚ)).order :=
  ModularCurve.ord_qInftyPlaceBar (AlgebraicClosure ℚ) _ f
end S_ModularCurve_ord_cuspInftyBar
end P2MW

public section
open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspInftyBar (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N) : (cuspInftyBar N).ord f = (f : LaurentSeries (AlgebraicClosure ℚ)).order := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_cuspInftyBar.solution
end
