import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_ringEquiv_of_isLocalization_of_comap_eq_of_comap_eq
attribute [-simp] AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply

set_option autoImplicit false

theorem AdicCompletion.exists_ringEquiv_of_isLocalization_of_comap_eq_of_comap_eq
    {A B Q : Type*} [CommRing A] [CommRing B] [CommRing Q] [Algebra A Q] [Algebra B Q]
    (M : Submonoid A) [IsLocalization M Q] (N : Submonoid B) [IsLocalization N Q]
    (P : Ideal A) [P.IsMaximal] (PB : Ideal B) [PB.IsMaximal]
    (𝔔 : Ideal Q) [𝔔.IsPrime]
    (hP : 𝔔.comap (algebraMap A Q) = P) (hPB : 𝔔.comap (algebraMap B Q) = PB) :
    ∃ T : AdicCompletion P A ≃+* AdicCompletion PB B,
      ∀ (a : A) (b : B), algebraMap A Q a = algebraMap B Q b →
        T (algebraMap A (AdicCompletion P A) a) = algebraMap B (AdicCompletion PB B) b := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_ringEquiv_of_isLocalization_of_comap_eq_of_comap_eq.solution
