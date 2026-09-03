import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_eq_of_forall_rpow_infinite_setOf_eval_eq

theorem MvPolynomial.eq_of_forall_rpow_infinite_setOf_eval_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ u : ℝ, u₀ < u →
      Set.Infinite {x : ℂ | MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q}) :
    P = Q := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_eq_of_forall_rpow_infinite_setOf_eval_eq.solution
