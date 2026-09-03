import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_isIntegrallyClosed_quotient_of_mem_minimalPrimes_of_forall_isMaximal_adicCompletion
attribute [-simp] AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply

set_option autoImplicit false

universe u

theorem Ideal.isIntegrallyClosed_quotient_of_mem_minimalPrimes_of_forall_isMaximal_adicCompletion
    (C : Type u) [CommRing C] [IsNoetherianRing C]
    (h : ∀ 𝔪 : Ideal C, 𝔪.IsMaximal → IsDomain (AdicCompletion 𝔪 C) ∧ IsIntegrallyClosed (AdicCompletion 𝔪 C))
    (𝔓 : Ideal C) (h𝔓 : 𝔓 ∈ (⊥ : Ideal C).minimalPrimes) :
    IsIntegrallyClosed (C ⧸ 𝔓) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_isIntegrallyClosed_quotient_of_mem_minimalPrimes_of_forall_isMaximal_adicCompletion.solution
