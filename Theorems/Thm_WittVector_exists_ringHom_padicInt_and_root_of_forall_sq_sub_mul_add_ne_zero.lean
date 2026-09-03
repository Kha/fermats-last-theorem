import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero

set_option autoImplicit false

theorem WittVector.exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero
    (p : ℕ) [Fact p.Prime] (t n : ℤ)
    (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0) :
    ∃ (ι : ℤ_[p] →+* WittVector p (GaloisField p 2)) (ω : WittVector p (GaloisField p 2)),
      (∀ c : ℤ_[p], WittVector.frobenius (ι c) = ι c) ∧
      ω * ω = (t : WittVector p (GaloisField p 2)) * ω - (n : WittVector p (GaloisField p 2)) ∧
      WittVector.frobenius ω = (t : WittVector p (GaloisField p 2)) - ω ∧
      (∀ c d : ℤ_[p], ι c + ι d * ω = 0 → c = 0 ∧ d = 0) ∧
      (∀ (k : ℕ) (x : WittVector p (GaloisField p 2)), ∃ c d : ℤ,
        x - ((c : WittVector p (GaloisField p 2)) + (d : WittVector p (GaloisField p 2)) * ω) ∈
          Ideal.span {((p : WittVector p (GaloisField p 2))) ^ k}) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero.solution
