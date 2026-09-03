import Definitions.Def_NumberField_IdeleProductMeasure
import P2M.Util
import P2M.Sol.S_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.Idele MeasureTheory
open scoped ENNReal

theorem NumberField.Idele.exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral
    (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧
      ∀ h : InfinitePlace F → ℝ → ℝ≥0∞, (∀ w, Measurable (h w)) →
        (∫⁻ a, ∏ w : InfinitePlace F, h w ‖((a : AdeleRing (𝓞 F) F).1 w)‖ ∂(sPartMeasure F ∅)) =
          C * ∏ w : InfinitePlace F, ∫⁻ t in Set.Ioi (0 : ℝ), h w t * (ENNReal.ofReal t)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral.solution
