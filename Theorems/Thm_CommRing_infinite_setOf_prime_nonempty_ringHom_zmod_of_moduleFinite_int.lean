import Mathlib
import P2M.Util
import P2M.Sol.S_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R] :
    {ℓ : ℕ | ℓ.Prime ∧ Nonempty (R →+* ZMod ℓ)}.Infinite := by p2m_exact_reverting @_root_.P2MW.S_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int.solution
