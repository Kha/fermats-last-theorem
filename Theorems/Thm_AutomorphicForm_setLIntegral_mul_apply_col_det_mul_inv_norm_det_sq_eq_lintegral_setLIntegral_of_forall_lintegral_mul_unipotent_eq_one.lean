import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem AutomorphicForm.setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one
    (A : Type) [NormedCommRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
    [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) (hμ : μ.IsAddHaarMeasure) (hA : ∀ᵐ a ∂μ, IsUnit a)
    (w : (Fin 2 → Fin 2 → A) → ℝ≥0∞) (hw : Measurable w)
    (hw1 : ∀ᵐ X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ).restrict
        {X | IsUnit (Matrix.of X).det},
      ∫⁻ x, w (Matrix.of.symm (Matrix.of X * !![(1 : A), x; 0, 1])) ∂μ = 1)
    (Ψ : (Fin 2 → A) × A → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ X in {X | IsUnit (Matrix.of X).det},
        w X * Ψ (fun i => X i 0, (Matrix.of X).det) *
          (ENNReal.ofReal |Algebra.norm ℝ (Matrix.of X).det| ^ 2)⁻¹
      ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
    ∫⁻ c, ∫⁻ δ in {δ | IsUnit δ}, Ψ (c, δ) * (ENNReal.ofReal |Algebra.norm ℝ δ| ^ 2)⁻¹ ∂μ
      ∂(Measure.pi fun _ : Fin 2 => μ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one.solution
