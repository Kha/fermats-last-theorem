import Mathlib
import P2M.Util
import P2M.Sol.S_AddChar_exists_completeOrthogonalIdempotents_forall_mul_eq_pow_mul_of_forall_isUnit_one_sub_pow

set_option autoImplicit false

universe u

theorem AddChar.exists_completeOrthogonalIdempotents_forall_mul_eq_pow_mul_of_forall_isUnit_one_sub_pow
    (R : Type u) [CommRing R] (N : ℕ) (hd : IsUnit ((N + 1 : ℕ) : R))
    (ζ : R) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] (hG : ∀ g : G, (N + 1) • g = 0) (χ : AddChar G R) :
    ∃ e : (G → Fin (N + 1)) → R, CompleteOrthogonalIdempotents e ∧
      ∀ k : G → Fin (N + 1), ∃ c : G →+ ZMod (N + 1), ∀ g : G, χ g * e k = ζ ^ (c g).val * e k := by p2m_exact_reverting @_root_.P2MW.S_AddChar_exists_completeOrthogonalIdempotents_forall_mul_eq_pow_mul_of_forall_isUnit_one_sub_pow.solution
