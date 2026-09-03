import Definitions.Def_AlgebraicGeometry_ThetaGroupAction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one
attribute [-instance] AlgebraicGeometry.Polarisation.ThetaPt.instMul AlgebraicGeometry.Polarisation.ThetaPt.instPowInt AlgebraicGeometry.Polarisation.ThetaPt.instDiv AlgebraicGeometry.Polarisation.ThetaPt.instGroup AlgebraicGeometry.Polarisation.ThetaPt.instInv AlgebraicGeometry.Polarisation.ThetaPt.instOne AlgebraicGeometry.Polarisation.PtGrp.instGroup AlgebraicGeometry.Polarisation.ThetaPt.instPowNat CategoryTheory.Pseudofunctor.CoGrothendieck.isIso_homMk GoodReductionJacobian.RelativeGroupLaw.AlgPoints.instAddCommGroup GoodReductionJacobian.RelativeGroupLaw.AlgPoints.instDistribMulAction GoodReductionJacobian.RelativeGroupLaw.AlgPoints.instInhabited GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] AlgebraicGeometry.Polarisation.ThetaPt.mul_pt AlgebraicGeometry.Polarisation.ThetaPt.ofScalar_pt AlgebraicGeometry.Polarisation.baseScalarHom_apply AlgebraicGeometry.Polarisation.ThetaPt.ofUnit_pt AlgebraicGeometry.Polarisation.translateIso_hom AlgebraicGeometry.Polarisation.ThetaPt.inv_pt AlgebraicGeometry.Polarisation.translateIso_inv AlgebraicGeometry.Polarisation.ThetaPt.one_pt AlgebraicGeometry.Scheme.Modules.fibration.autOfIso_hom_fiber AlgebraicGeometry.Scheme.Modules.fibration.autOfIso_hom_base AlgebraicGeometry.Scheme.Modules.homothety_app AlgebraicGeometry.Polarisation.ThetaPt.ptHom_apply AlgebraicGeometry.Scheme.Modules.fibration_map_toFunctor CategoryTheory.Pseudofunctor.CoGrothendieck.homMk_base CategoryTheory.Pseudofunctor.CoGrothendieck.isoMk_hom AlgebraicGeometry.RiemannForm.thetaGroup.pt_liftOfIso AlgebraicGeometry.RiemannForm.modulePair_fiber AlgebraicGeometry.RiemannForm.pt_levelLift AlgebraicGeometry.RiemannForm.modulePair_base AlgebraicGeometry.RiemannForm.thetaGroup.pt_apply AlgebraicGeometry.RiemannForm.translationIso_hom AlgebraicGeometry.Scheme.Modules.fibration_obj CategoryTheory.Pseudofunctor.CoGrothendieck.homMk_fiber AlgebraicGeometry.RiemannForm.ofUnitPt_toUnitPt AlgebraicGeometry.RiemannForm.toUnitPt_coe AlgebraicGeometry.RiemannForm.toUnitPt_ofUnitPt AlgebraicGeometry.RiemannForm.ofUnitPt_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.ofPoint_toPoint GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint_map_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.torsionByEquiv_symm_apply_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint_ofPoint GoodReductionJacobian.RelativeGroupLaw.AlgPoints.torsionByEquiv_apply_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.equivPoint_symm_apply GoodReductionJacobian.RelativeGroupLaw.AlgPoints.mapPoint_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint_smul_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.equivPoint_apply NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left
attribute [-simp] NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {m : ℕ} (ε : Fin m → R) (hε : ∀ j, IsIdempotentElem (ε j)) (hsum : ∑ j, ε j = 1)
    (horth : ∀ j l, j ≠ l → ε j * ε l = 0)
    (b : ∀ j, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ⟶ pullback f t)
    (hb₁ : ∀ j, b j ≫ pullback.fst f t =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))
    (hb₂ : ∀ j, b j ≫ pullback.snd f t =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))))
    (c : ∀ j, (Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
      (Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))).obj 𝓛)
    (θ' : ∀ j, ThetaPt f L 𝓛 (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t)) :
    ∃ θ : ThetaPt f L 𝓛 t,
      (∀ j, (θ' j).pt.1 = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ θ.pt.1) ∧
      (∀ j (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
        (θ' j).act ((c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) s :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          (c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) (θ.act s) :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) ∧
      (∀ s s' : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤),
        (∀ j, (θ' j).act ((c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) s :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          (c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) s' :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) →
        θ.act s = s') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one.solution
