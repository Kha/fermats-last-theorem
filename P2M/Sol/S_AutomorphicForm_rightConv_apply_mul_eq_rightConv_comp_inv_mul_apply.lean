import Definitions.Def_AutomorphicForm_RightConvolution
import P2M.Util
namespace P2MW.S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply

open NumberField
open MeasureTheory AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f (g * t) = rightConv K φ (fun y => f (t⁻¹ * y)) g := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  show (∫ x, φ (g * t * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      = ∫ x, φ (g * x) * f (t⁻¹ * x) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  have h := integral_mul_left_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
    (fun x => φ (g * x) * f (t⁻¹ * x)) t
  simp only [inv_mul_cancel_left] at h
  simpa only [mul_assoc] using h
