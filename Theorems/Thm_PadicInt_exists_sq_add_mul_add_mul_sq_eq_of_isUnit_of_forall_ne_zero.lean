import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_exists_sq_add_mul_add_mul_sq_eq_of_isUnit_of_forall_ne_zero

set_option autoImplicit false

theorem PadicInt.exists_sq_add_mul_add_mul_sq_eq_of_isUnit_of_forall_ne_zero
    (p : ℕ) [Fact p.Prime] (t n : ℤ)
    (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0)
    (u : ℤ_[p]) (hu : IsUnit u) :
    ∃ c d : ℤ_[p], c ^ 2 + (t : ℤ_[p]) * c * d + (n : ℤ_[p]) * d ^ 2 = u := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_sq_add_mul_add_mul_sq_eq_of_isUnit_of_forall_ne_zero.solution
