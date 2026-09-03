import Definitions.Def_ModularCurve_JZeroHeightForm
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_heightForm_single

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.heightForm_single (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hv : v ≠ cuspInftyBar N) (n : ℤ) :
    JZero.heightForm N s (Finsupp.single v n)
      = (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) * (n : ℝ) ^ 2
          * baseHt s (cuspInftyBar N) v := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_heightForm_single.solution
