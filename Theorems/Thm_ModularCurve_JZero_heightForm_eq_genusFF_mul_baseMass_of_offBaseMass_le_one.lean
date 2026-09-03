import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ v, 0 ≤ D v)
    (hm : offBaseMass N D ≤ 1) :
    heightForm N s D = (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) * baseMass N s D := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one.solution
