import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_baseChange_surjective_and_fibre
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPoints_baseChange_surjective_and_fibre
    {R : Type u} [CommRing R]
    {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase)
    (𝒱 : X.TwoAffineOpenCover)
    (A : Type u) [CommRing A] [Algebra R A] (hA : Function.Surjective (algebraMap R A))
    (q : ℕ) (hq : RingHom.ker (algebraMap R A) = Ideal.span {(q : R)}) :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let tR := Scheme.TwoAffineOpenCover.specMap R (DualNumber R)
    let tA := Scheme.TwoAffineOpenCover.specMap R (DualNumber A)
    let σ := (RelPicard.LFP.stageHom R (DualNumber.lift ⟨(Algebra.ofId R (DualNumber A), DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).1

    (∀ x : SchemeHomOver tR D.toBase,
        dualNumberReduction R R ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 →
          dualNumberReduction R A ≫ (σ ≫ x.1) = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1) ∧

    (∀ x y : SchemeHomOver tR D.toBase,
        σ ≫ (L.mul tR x y).1 =
          (L.mul tA ⟨σ ≫ x.1, by rw [Category.assoc, x.2]; exact (RelPicard.LFP.stageHom R (DualNumber.lift ⟨(Algebra.ofId R (DualNumber A), DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).2⟩
            ⟨σ ≫ y.1, by rw [Category.assoc, y.2]; exact (RelPicard.LFP.stageHom R (DualNumber.lift ⟨(Algebra.ofId R (DualNumber A), DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).2⟩).1) ∧

    (∀ (φ : SchemeHomOver D.toBase D.toBase) (x : SchemeHomOver tR D.toBase), σ ≫ (x.1 ≫ φ.1) = (σ ≫ x.1) ≫ φ.1) ∧

    (∀ y : SchemeHomOver tA D.toBase,
        dualNumberReduction R A ≫ y.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1 →
          ∃ x : SchemeHomOver tR D.toBase,
            dualNumberReduction R R ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 ∧ σ ≫ x.1 = y.1) ∧

    (∀ x x' : SchemeHomOver tR D.toBase,
        dualNumberReduction R R ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 →
        dualNumberReduction R R ≫ x'.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 →
          (σ ≫ x.1 = σ ≫ x'.1 ↔
            ∃ z : SchemeHomOver tR D.toBase,
              dualNumberReduction R R ≫ z.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 ∧ x' = L.mul tR x (L.nsmul tR q z))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_baseChange_surjective_and_fibre.solution
