import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul

set_option autoImplicit false

theorem WittVector.exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul
    (p : ℕ) [Fact p.Prime] :
    ∃ (r : WittVector p (GaloisField p 2) →+* Matrix (Fin 2) (Fin 2) ℤ_[p])
      (S : Matrix (Fin 2) (Fin 2) ℤ_[p]),
      S * S = 1 ∧
      (∀ a, S * r a = r (WittVector.frobenius a) * S) ∧
      (∀ a c, r a + r c * S = 0 → a = 0 ∧ c = 0) ∧
      (∀ M : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ a c, M = r a + r c * S) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul.solution
