import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two

set_option autoImplicit false

theorem IsIntegrallyClosed.isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀] [IsIntegrallyClosed R₀]
    (hdim : ringKrullDim R₀ ≤ (2 : WithBot ℕ∞))
    (𝔯 : Ideal R₀) [𝔯.IsPrime] (h𝔯 : 𝔯 ≠ IsLocalRing.maximalIdeal R₀) :
    IsRegularLocalRing (Localization.AtPrime 𝔯) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two.solution
