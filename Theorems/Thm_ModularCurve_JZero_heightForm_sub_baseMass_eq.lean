import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_heightForm_sub_baseMass_eq

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.heightForm_sub_baseMass_eq (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    JZero.heightForm N s D - baseMass N s D
      = ((D.erase (cuspInftyBar N)).sum fun v n =>
          (((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
              + (offBaseMass N D : ℝ) - 2) * (n : ℝ)
            + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
              * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)
        - ((D.erase (cuspInftyBar N)).sum fun v n => ((D.erase (cuspInftyBar N)).erase v).sum fun w k =>
            (n : ℝ) * (k : ℝ) * pairHt s v w) / 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_heightForm_sub_baseMass_eq.solution
