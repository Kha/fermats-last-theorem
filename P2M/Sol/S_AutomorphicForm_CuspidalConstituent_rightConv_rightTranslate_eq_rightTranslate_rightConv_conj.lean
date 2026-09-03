import Mathlib
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import P2M.Util
namespace P2MW.S_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem solution
    (F : Type) [Field F] [NumberField F]
    (h : AdelicGL2 (𝓞 F) F) (φ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (rightTranslate F h φ) f = rightTranslate F h (rightConv F φ (fun y => f (h * y * h⁻¹))) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  funext g
  show (∫ x, rightTranslate F h φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F))
      = ∫ x, φ (g * h * x) * f (h * x * h⁻¹) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
  simp only [rightTranslate_apply]

  have h1 := integral_mul_left_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    (fun x => φ (g * h * x) * f (h * x * h⁻¹)) h⁻¹
  simp only [← mul_assoc, mul_inv_cancel_right, mul_inv_cancel, one_mul] at h1

  have h2 := integral_mul_right_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    (fun x => φ (g * x) * f (x * h⁻¹)) h
  simp only [mul_inv_cancel_right, ← mul_assoc] at h2

  rw [h2, h1]
