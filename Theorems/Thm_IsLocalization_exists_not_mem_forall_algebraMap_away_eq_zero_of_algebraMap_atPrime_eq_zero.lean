import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalization_exists_not_mem_forall_algebraMap_away_eq_zero_of_algebraMap_atPrime_eq_zero

set_option autoImplicit false

universe u

theorem IsLocalization.exists_not_mem_forall_algebraMap_away_eq_zero_of_algebraMap_atPrime_eq_zero
    {S : Type u} [CommRing S] [IsNoetherianRing S] (𝔭 : PrimeSpectrum S) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧ ∀ x : S, algebraMap S (Localization.AtPrime 𝔭.asIdeal) x = 0 →
      algebraMap S (Localization.Away g) x = 0 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalization_exists_not_mem_forall_algebraMap_away_eq_zero_of_algebraMap_atPrime_eq_zero.solution
