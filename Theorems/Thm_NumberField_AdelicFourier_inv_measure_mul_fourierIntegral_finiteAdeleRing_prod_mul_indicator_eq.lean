import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain MeasureTheory
open scoped Classical

theorem NumberField.AdelicFourier.inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ) (hψf : Continuous ψf)
    (ψv : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ) (hψv : ∀ v, Continuous (ψv v))
    (hprod : ∀ x : FiniteAdeleRing (𝓞 F) F, ψf x = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
    (hunr : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v z = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (w : FiniteAdeleRing (𝓞 F) F) :
    ((ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ))⁻¹ *
        fourierIntegral ψf ν
          (fun x => (∏ v ∈ S, h v (x v)) *
            (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then 1 else 0)) w
      = (∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹ *
            fourierIntegral (ψv v) (μ v) (h v) (w v)) *
        (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
              ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * w v) = 1
          then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq.solution
