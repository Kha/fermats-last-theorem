import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_eq_of_forall_eval_rpow_eq

theorem MvPolynomial.eq_of_forall_eval_rpow_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (S : Set ℂ)
    (hS : S.Infinite) (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ x ∈ S, ∀ u : ℝ, u₀ < u →
      MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q) :
    P = Q := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_eq_of_forall_eval_rpow_eq.solution
