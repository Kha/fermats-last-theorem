import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite

set_option autoImplicit false

theorem Complex.forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
    (q : ℕ) (hq : 1 < q) (P Q₁ Q₂ : Polynomial ℂ) (hQ₂ : Q₂ ≠ 0) (m k : ℤ) (γ Zd : ℂ → ℂ) (S S₁ : Set ℂ)
    (hS : {t : ℝ | (t : ℂ) ∈ S}.Infinite)
    (h : ∀ s ∈ S,
      (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s))
    (h₁ : ∀ s ∈ S₁,
      Zd s * Q₂.eval ((q : ℂ) ^ (-s)) = Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) * γ s) :
    (∀ s : ℂ, (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s)) ∧
    ∃ R : Finset ℝ, ∀ s ∈ S₁, (q : ℝ) ^ (-s.re) ∉ R →
      Zd s = γ s * ((q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s))) := by p2m_exact_reverting @_root_.P2MW.S_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite.solution
