import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne
    (m : ℕ) {k : ℤ} (hk : k = 12 * (m : ℤ))
    (h : ModularForm (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range k) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑h : UpperHalfPlane → ℂ)) =
        Polynomial.aeval (ModularCurve.jqModC ℂ) P *
          ModularCurve.intSeriesC ℂ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ m) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne.solution
