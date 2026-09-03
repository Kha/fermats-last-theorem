import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero

set_option autoImplicit false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [Fact p.Prime]
    (j : ↥F₀) [Fact (j ≠ 0)]
    (hj : ∀ n : ℤ, n ≤ 0 → ((j : LaurentSeries ℚ)⁻¹).coeff n = 0) :
    ∃ ε : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p),
      ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
        (∀ n : ℤ, n < 0 → ((b : ↥F₀) : LaurentSeries ℚ).coeff n = 0) ∧
        ((ε b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = ((b : ↥F₀) : LaurentSeries ℚ).coeff 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero.solution
