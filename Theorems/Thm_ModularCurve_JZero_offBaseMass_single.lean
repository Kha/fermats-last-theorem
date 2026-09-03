import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_offBaseMass_single

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.offBaseMass_single (N : ℕ) [NeZero N] {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : v ≠ cuspInftyBar N) (n : ℤ) :
    offBaseMass N (Finsupp.single v n) = n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_offBaseMass_single.solution
