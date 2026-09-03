import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
attribute [-simp] AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply
set_option autoImplicit false

theorem AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
    {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (𝔓 : Ideal B) [𝔓.IsMaximal] [IsLocalRing S] [IsLocalization.AtPrime S 𝔓] :
    ∃ T : AdicCompletion 𝔓 B ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ b : B, T (algebraMap B (AdicCompletion 𝔓 B) b)
        = algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap B S b) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal.solution
