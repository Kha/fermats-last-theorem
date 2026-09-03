import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_NumberField_Idele_integrable_sPartMeasure_of_norm_le_mul_prod

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel in

theorem NumberField.Idele.integrable_sPartMeasure_of_norm_le_mul_prod
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (νA : Measure (InfiniteAdeleRing F)ˣ) [νA.IsHaarMeasure]
    [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)ˣ]
    [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)ˣ]
    (μ : ∀ w : HeightOneSpectrum (𝓞 F), Measure (w.adicCompletion F)ˣ)
    (hμ : ∀ w ∈ S, (μ w).IsHaarMeasure)
    (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (g : (InfiniteAdeleRing F)ˣ → ℝ)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ → ℝ)
    (hg : 0 ≤ g) (hh : ∀ w ∈ S, 0 ≤ h w)
    (hgm : AEStronglyMeasurable g νA) (hhm : ∀ w ∈ S, AEStronglyMeasurable (h w) (μ w))
    (hgi : HasFiniteIntegral g νA) (hhi : ∀ w ∈ S, HasFiniteIntegral (h w) (μ w))
    (hfm : AEStronglyMeasurable f (NumberField.Idele.sPartMeasure F S))
    (hdom : ∀ a : (AdeleRing (𝓞 F) F)ˣ,
      (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) →
        ‖f a‖ ≤ g (M4aHerbrand.infPart a) * ∏ w ∈ S, h w (M4aHerbrand.finPart w a)) :
    Integrable f (NumberField.Idele.sPartMeasure F S) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_integrable_sPartMeasure_of_norm_le_mul_prod.solution
