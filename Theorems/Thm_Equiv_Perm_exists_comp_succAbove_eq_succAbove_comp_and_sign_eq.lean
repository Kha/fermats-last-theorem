import Mathlib
import P2M.Util
import P2M.Sol.S_Equiv_Perm_exists_comp_succAbove_eq_succAbove_comp_and_sign_eq

set_option autoImplicit false
theorem Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    ∃ τ : Equiv.Perm (Fin n), (∀ k : Fin n, σ (j.succAbove k) = (σ j).succAbove (τ k)) ∧
      Equiv.Perm.sign σ = (-1) ^ ((j : ℕ) + ((σ j) : ℕ)) * Equiv.Perm.sign τ := by p2m_exact_reverting @_root_.P2MW.S_Equiv_Perm_exists_comp_succAbove_eq_succAbove_comp_and_sign_eq.solution
