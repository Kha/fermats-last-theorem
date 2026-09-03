import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq

set_option autoImplicit false

universe u

theorem WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq
    {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ nonZeroDivisors R)
    (n : ℕ) (x y : WittVector p R)
    (h : ∀ k < n, WittVector.ghostComponent k x = WittVector.ghostComponent k y) :
    ∀ k < n, x.coeff k = y.coeff k := by p2m_exact_reverting @_root_.P2MW.S_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq.solution
