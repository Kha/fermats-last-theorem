import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing
    {C C' : Type} [CommRing C] [IsLocalRing C] [CommRing C'] [Algebra C C']
    (𝔫 : Ideal C') [𝔫.IsMaximal]
    (hle : (maximalIdeal C).map (algebraMap C C') ≤ 𝔫)
    [IsReduced (C' ⧸ (maximalIdeal C).map (algebraMap C C'))]
    [IsArtinianRing (C' ⧸ (maximalIdeal C).map (algebraMap C C'))] :
    (maximalIdeal C).map (algebraMap C (Localization.AtPrime 𝔫)) = maximalIdeal (Localization.AtPrime 𝔫) ∧
    IsLocalHom (algebraMap C (Localization.AtPrime 𝔫)) ∧
    Function.Surjective ((residue (Localization.AtPrime 𝔫)).comp (algebraMap C' (Localization.AtPrime 𝔫))) ∧
    RingHom.ker ((residue (Localization.AtPrime 𝔫)).comp (algebraMap C' (Localization.AtPrime 𝔫))) = 𝔫 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing.solution
