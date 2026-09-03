import Definitions.Def_NumberField_IdeleProductMeasure
import P2M.Util
import P2M.Sol.S_NumberField_Idele_lintegral_mul_finprod_eq_lintegral_sPartMeasure_mul_iSup

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.Idele MeasureTheory
open scoped ENNReal

theorem NumberField.Idele.lintegral_mul_finprod_eq_lintegral_sPartMeasure_mul_iSup
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hf : Measurable[ideleBorel F] f)
    (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) (hφ : ∀ v, v ∉ S → φ v 0 = 1) :
    (∫⁻ a, f (partAt F S a) * (∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ S), φ v (ord F v a))
        ∂(idelicHaar F)) =
      (∫⁻ a, f a ∂(sPartMeasure F S)) *
        ⨆ (L : Finset (HeightOneSpectrum (𝓞 F))) (_ : Disjoint L S), ∏ v ∈ L, ∑' m : ℤ, φ v m := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_lintegral_mul_finprod_eq_lintegral_sPartMeasure_mul_iSup.solution
