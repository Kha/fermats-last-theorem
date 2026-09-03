import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import P2M.Util
import P2M.Sol.S_AutomorphicForm_peterssonIntegral_rightConv_eq_integral_mul_peterssonIntegral_translate

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.peterssonIntegral_rightConv_eq_integral_mul_peterssonIntegral_translate
    (K : Type) [Field K] [NumberField K]
    [SigmaFinite (adelicGLHaar (Fin 2) (𝓞 K) K)]
    (w : ℝ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (_h𝓕 : MeasurableSet 𝓕)
    (Φ f Y X Ψ h : AdelicGL2 (𝓞 K) K → ℂ) :
    (Integrable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        Φ (p.1 * p.2) * f p.2 * (starRingEnd ℂ) (Y p.1) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ))
        (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕).prod (adelicGLHaar (Fin 2) (𝓞 K) K)) →
      peterssonIntegral K w 𝓕 (rightConv K Φ f) Y =
        ∫ x, f x * peterssonIntegral K w 𝓕 (fun g => Φ (g * x)) Y ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (Integrable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        X p.1 * (starRingEnd ℂ) (Ψ (p.1 * p.2) * h p.2) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ))
        (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕).prod (adelicGLHaar (Fin 2) (𝓞 K) K)) →
      peterssonIntegral K w 𝓕 X (rightConv K Ψ h) =
        ∫ x, (starRingEnd ℂ) (h x) * peterssonIntegral K w 𝓕 X (fun g => Ψ (g * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_peterssonIntegral_rightConv_eq_integral_mul_peterssonIntegral_translate.solution
