import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_EisensteinGeneral_Factorization_inv_measure_mul_setIntegral_integralOffSet_finprod_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox
  IsDedekindDomain

theorem EisensteinGeneral.Factorization.inv_measure_mul_setIntegral_integralOffSet_finprod_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1) :
    (ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * ∫ x in {x : FiniteAdeleRing (𝓞 F) F |
              ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F},
            ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν
      = ∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
          * ∫ y, h v y ∂(μ v)) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinGeneral_Factorization_inv_measure_mul_setIntegral_integralOffSet_finprod_eq.solution
