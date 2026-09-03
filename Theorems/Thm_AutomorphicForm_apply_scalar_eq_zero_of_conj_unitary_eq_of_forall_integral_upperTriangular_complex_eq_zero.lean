import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero
    (F : (Fin 2 → Fin 2 → ℂ) → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hinv : ∀ u : Matrix (Fin 2) (Fin 2) ℂ, u ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      ∀ E : Fin 2 → Fin 2 → ℂ, F (Matrix.of.symm (u * Matrix.of E * star u)) = F E)
    (c : ℂ) (hc : c ≠ 0)
    (hvan : ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, w ≠ 0 → ‖w‖ < ε →
      ∫ v : ℂ, F (Matrix.of.symm !![c * Complex.exp w, v; 0, c * Complex.exp (-w)]) = 0) :
    F (Matrix.of.symm !![c, 0; 0, c]) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero.solution
