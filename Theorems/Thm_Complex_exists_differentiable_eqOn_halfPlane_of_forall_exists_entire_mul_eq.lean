import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_differentiable_eqOn_halfPlane_of_forall_exists_entire_mul_eq

set_option autoImplicit false

theorem Complex.exists_differentiable_eqOn_halfPlane_of_forall_exists_entire_mul_eq
    (L : ℂ → ℂ) (σ : ℝ) (hL : ContinuousOn L {s : ℂ | σ < s.re})
    (h : ∀ s₁ : ℂ, ∃ (Z E : ℂ → ℂ) (c : ℂ) (σ' : ℝ), Differentiable ℂ Z ∧ Differentiable ℂ E ∧ c ≠ 0 ∧
      E s₁ ≠ 0 ∧ ∀ s : ℂ, σ' < s.re → Z s = c * E s * L s) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∃ σ'' : ℝ, ∀ s : ℂ, σ'' < s.re → Λ s = L s := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_differentiable_eqOn_halfPlane_of_forall_exists_entire_mul_eq.solution
