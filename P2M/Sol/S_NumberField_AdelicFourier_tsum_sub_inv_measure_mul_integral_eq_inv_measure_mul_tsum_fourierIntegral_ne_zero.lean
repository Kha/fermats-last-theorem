import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral
import Theorems.Thm_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
import P2M.Util
namespace P2MW.S_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        - ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ * ∫ v, f v ∂μ
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : {ξ : F // ξ ≠ 0}, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  have hsum : Summable fun ξ : F ↦ fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
    have := summable_translate_of_mem_schwartzBruhat F
      (fourierIntegral_mem_schwartzBruhat F μ hψ hf) 0
    simpa only [zero_add] using this
  have key : ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) 0)
        + ∑' ξ : {ξ : F // ξ ≠ 0}, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
    rw [← hsum.sum_add_tsum_subtype_compl {0}, Finset.sum_singleton]
    congr 1
    exact tsum_congr_subtype
      (fun ξ : F ↦ fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ)) fun x ↦ by simp
  have h0 : fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) 0) = ∫ v, f v ∂μ := by
    simp [fourierIntegral_def]
  rw [tsum_eq_inv_measure_mul_tsum_fourierIntegral F μ hψ hf, key, h0]
  ring
