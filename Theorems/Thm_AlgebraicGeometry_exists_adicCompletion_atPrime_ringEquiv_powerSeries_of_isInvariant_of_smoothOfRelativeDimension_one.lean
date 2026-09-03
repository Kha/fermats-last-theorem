import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [IsAlgClosed (ResidueField W)]
    {S A : Type} [CommRing S] [CommRing A] [Algebra W S] [Algebra W A] [Algebra S A] [IsScalarTower W S A]
    [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G W A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap W A)))]
    (𝔮 : Ideal S) [𝔮.IsMaximal] [𝔮.LiesOver (maximalIdeal W)] :
    ∃ e : AdicCompletion (maximalIdeal (Localization.AtPrime 𝔮)) (Localization.AtPrime 𝔮) ≃+* PowerSeries W,
      ∀ a : W, e (algebraMap (Localization.AtPrime 𝔮) _
          (algebraMap S (Localization.AtPrime 𝔮) (algebraMap W S a))) = PowerSeries.C a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one.solution
