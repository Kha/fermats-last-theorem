import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_moduleFinite_of_isUnramifiedAt
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

theorem IsLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_moduleFinite_of_isUnramifiedAt
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀] [IsIntegrallyClosed R₀]
    (hdimR : ringKrullDim R₀ ≤ (2 : WithBot ℕ∞))
    {S : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsLocalRing S] [IsIntegrallyClosed S]
    (hdimS : ringKrullDim S ≤ (2 : WithBot ℕ∞)) (hdimS' : 2 ≤ ringKrullDim S)
    (t : S) (ht : t ∈ IsLocalRing.maximalIdeal S) (ht0 : t ≠ 0)
    [Algebra R₀ (AdicCompletion (IsLocalRing.maximalIdeal S) S)]
    [Module.Finite R₀ (AdicCompletion (IsLocalRing.maximalIdeal S) S)]
    [FaithfulSMul R₀ (AdicCompletion (IsLocalRing.maximalIdeal S) S)]
    (hunr : ∀ (𝔓 : Ideal (AdicCompletion (IsLocalRing.maximalIdeal S) S)) [𝔓.IsPrime], ¬ 𝔓.IsMaximal →
      Algebra.IsUnramifiedAt R₀ 𝔓) :
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_moduleFinite_of_isUnramifiedAt.solution
