import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel in

theorem NumberField.Idele.exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (νA : Measure (InfiniteAdeleRing F)ˣ) [νA.IsHaarMeasure]
    [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)ˣ]
    [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)ˣ]
    (μ : ∀ w : HeightOneSpectrum (𝓞 F), Measure (w.adicCompletion F)ˣ)
    (hμ : ∀ w ∈ S, (μ w).IsHaarMeasure) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (g : (InfiniteAdeleRing F)ˣ → ℂ)
        (h : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ → ℂ),
        (∀ a : (AdeleRing (𝓞 F) F)ˣ,
          (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) →
            f a = g (M4aHerbrand.infPart a) * ∏ w ∈ S, h w (M4aHerbrand.finPart w a)) →
        AEStronglyMeasurable f (NumberField.Idele.sPartMeasure F S) →
          ∫ a, f a ∂(NumberField.Idele.sPartMeasure F S) =
            c * (∫ u, g u ∂νA) * ∏ w ∈ S, ∫ t, h w t ∂(μ w) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.solution
