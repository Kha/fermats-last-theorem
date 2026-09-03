import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_add_coeff_eq_of_forall_coeff_eq_zero

set_option autoImplicit false

universe u

theorem WittVector.add_coeff_eq_of_forall_coeff_eq_zero
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] (x y : WittVector p S) (r : ℕ)
    (hx : ∀ i : ℕ, i < r → x.coeff i = 0) :
    ∀ i : ℕ, i < r → (x + y).coeff i = y.coeff i := by p2m_exact_reverting @_root_.P2MW.S_WittVector_add_coeff_eq_of_forall_coeff_eq_zero.solution
