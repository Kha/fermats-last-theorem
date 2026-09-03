import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_baseMass_single

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.baseMass_single (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hv : v ≠ cuspInftyBar N) (n : ℤ) :
    baseMass N s (Finsupp.single v n) = (n : ℝ) * baseHt s (cuspInftyBar N) v := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_baseMass_single.solution
