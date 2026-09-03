import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_offBaseMass_add_single_cuspInftyBar

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.offBaseMass_add_single_cuspInftyBar (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (m : ℤ) :
    offBaseMass N (D + Finsupp.single (cuspInftyBar N) m) = offBaseMass N D := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_offBaseMass_add_single_cuspInftyBar.solution
