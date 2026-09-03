import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import P2M.Util
import P2M.Sol.S_AdicCompletion_isDomain_and_isIntegrallyClosed_adicCompletion_maximalIdeal_of_isLocalization_atPrime

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.isDomain_and_isIntegrallyClosed_adicCompletion_maximalIdeal_of_isLocalization_atPrime {O : Type} [CommRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [Algebra O C] (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫]
    (hd : IsDomain (AdicCompletion 𝔫 C)) (hn : IsIntegrallyClosed (AdicCompletion 𝔫 C)) :
    IsDomain (AdicCompletion (maximalIdeal S) S) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal S) S) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_isDomain_and_isIntegrallyClosed_adicCompletion_maximalIdeal_of_isLocalization_atPrime.solution
