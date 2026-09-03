import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_LatticeHeckeFamily
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_dualNumber_kernel_equiv_addMonoidHom_intLattice_baseChange_of_surjective_of_ker_eq_span
attribute [-instance] AlgebraicGeometry.RelPicard.RigKerDualNumber.setoid AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian ModularCurve IsLocalRing CuspForm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_dualNumber_kernel_equiv_addMonoidHom_intLattice_baseChange_of_surjective_of_ker_eq_span
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt p) c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase)
    (𝒱 : X.TwoAffineOpenCover)
    (φ : HeckeAlg → SchemeHomOver D.toBase D.toBase)

    (hφL : letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
      ∀ (t : HeckeAlg) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
        (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) (φ t) =
        L.mul s (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (A : Type) [CommRing A] [Algebra ↥(GaloisRep.ratLocalizedAt p) A]
    (hA : Function.Surjective (algebraMap ↥(GaloisRep.ratLocalizedAt p) A))
    (hker : RingHom.ker (algebraMap ↥(GaloisRep.ratLocalizedAt p) A) =
      Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}) :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    letI := (CuspForm.latticeHeckeFamily N).module
    ∀ τ : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1} ≃
          (↥(CuspForm.intLattice N 2) →+ ↥(GaloisRep.ratLocalizedAt p)),
      (∀ x y z : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1},
          z.1 = L.mul _ x.1 y.1 → τ z = τ x + τ y) →
      (∀ (t : HeckeAlg) (x y : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1}),
          y.1.1 = x.1.1 ≫ (φ t).1 → ∀ g : ↥(CuspForm.intLattice N 2), τ y g = τ x (t • g)) →
      ∃ τk : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber A)))) D.toBase //
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)))).1} ≃
          (↥(CuspForm.intLattice N 2) →+ A),

        (∀ x y z : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber A)))) D.toBase //
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)))).1},
          z.1 = L.mul _ x.1 y.1 → τk z = τk x + τk y) ∧

        (∀ (β : DualNumber ↥(GaloisRep.ratLocalizedAt p) →+* DualNumber A)
          (x : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1})
          (xk : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber A)))) D.toBase //
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)))).1}),
          β.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber A) →
          β DualNumber.eps = DualNumber.eps →
          xk.1.1 = Spec.map (CommRingCat.ofHom β) ≫ x.1.1 →
          ∀ g : ↥(CuspForm.intLattice N 2), τk xk g = algebraMap ↥(GaloisRep.ratLocalizedAt p) A (τ x g)) ∧

        (∀ (t : HeckeAlg) (x y : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber A)))) D.toBase //
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)))).1}),
          y.1.1 = x.1.1 ≫ (φ t).1 → ∀ g : ↥(CuspForm.intLattice N 2), τk y g = τk x (t • g)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_dualNumber_kernel_equiv_addMonoidHom_intLattice_baseChange_of_surjective_of_ker_eq_span.solution
