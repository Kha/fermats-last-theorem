import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_exists_forall_eq_pow_prime_pow_of_ker_eq_of_finite_range

set_option autoImplicit false
theorem RingHom.exists_forall_eq_pow_prime_pow_of_ker_eq_of_finite_range
    {T L : Type} [CommRing T] [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (f₁ f₂ : T →+* L) (hker : RingHom.ker f₁ = RingHom.ker f₂)
    (hfin : (Set.range f₁).Finite) :
    ∃ j : ℕ, ∀ t : T, f₂ t = f₁ t ^ p ^ j := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_forall_eq_pow_prime_pow_of_ker_eq_of_finite_range.solution
