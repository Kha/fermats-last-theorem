import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral

open NumberField NumberField.AdelicFourier AutomorphicForm
theorem NumberField.AdelicFourier.tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) (x : AdeleRing (𝓞 F) F) :
    ∑' ξ : F, f (x + algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) * ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ * x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral.solution
