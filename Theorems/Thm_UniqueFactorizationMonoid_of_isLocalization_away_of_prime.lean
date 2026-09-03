import Mathlib
import P2M.Util
import P2M.Sol.S_UniqueFactorizationMonoid_of_isLocalization_away_of_prime

set_option autoImplicit false

theorem UniqueFactorizationMonoid.of_isLocalization_away_of_prime
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {x : R} (hx : Prime x)
    (S : Type*) [CommRing S] [IsDomain S] [Algebra R S] [IsLocalization.Away x S]
    [UniqueFactorizationMonoid S] : UniqueFactorizationMonoid R := by p2m_exact_reverting @_root_.P2MW.S_UniqueFactorizationMonoid_of_isLocalization_away_of_prime.solution
