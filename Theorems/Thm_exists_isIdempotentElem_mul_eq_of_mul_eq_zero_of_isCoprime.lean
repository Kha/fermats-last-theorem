import Mathlib
import P2M.Util
import P2M.Sol.S_exists_isIdempotentElem_mul_eq_of_mul_eq_zero_of_isCoprime

set_option autoImplicit false

universe u

theorem exists_isIdempotentElem_mul_eq_of_mul_eq_zero_of_isCoprime
    {R : Type u} [CommRing R] {f g : R} (hfg : f * g = 0) (hcop : IsCoprime f g) :
    ∃ e w : R, IsIdempotentElem e ∧ IsUnit w ∧ f = e * w := by p2m_exact_reverting @_root_.P2MW.S_exists_isIdempotentElem_mul_eq_of_mul_eq_zero_of_isCoprime.solution
