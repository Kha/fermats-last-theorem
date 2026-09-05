module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Sol.S_ModularCurve_deg_qInftyPlaceBar
import P2M.Util

namespace P2MW.S_ModularCurve_deg_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] :
    (cuspInftyBar N).deg = 1 :=
  ModularCurve.deg_qInftyPlaceBar (AlgebraicClosure ℚ) _
end S_ModularCurve_deg_cuspInftyBar
end P2MW

public section
open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_cuspInftyBar (N : ℕ) [NeZero N] : (cuspInftyBar N).deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_deg_cuspInftyBar.solution
end
