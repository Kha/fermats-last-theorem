import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_localization_atPrime_of_adicCompletion

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsIntegrallyClosed.localization_atPrime_of_adicCompletion
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] (𝔪 : Ideal R) [𝔪.IsMaximal]
    [IsDomain (AdicCompletion 𝔪 R)] [IsIntegrallyClosed (AdicCompletion 𝔪 R)] :
    IsIntegrallyClosed (Localization.AtPrime 𝔪) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_localization_atPrime_of_adicCompletion.solution
