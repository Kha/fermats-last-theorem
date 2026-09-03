import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two

set_option autoImplicit false

universe u

theorem WittVector.eq_or_eq_comp_frobenius_of_ringHom_galoisField_two
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (a b : WittVector p (GaloisField p 2) →+* WittVector p k) :
    a = b ∨
      a = b.comp (WittVector.frobenius : WittVector p (GaloisField p 2) →+* WittVector p (GaloisField p 2)) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two.solution
