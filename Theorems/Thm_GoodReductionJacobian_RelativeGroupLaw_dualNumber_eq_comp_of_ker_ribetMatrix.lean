import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_dualNumber_eq_comp_of_ker_ribetMatrix
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.dualNumber_eq_comp_of_ker_ribetMatrix
    {κ : Type u} [Field κ] {B : Scheme.{u}} (sB : B ⟶ Spec (CommRingCat.of κ)) (L : RelativeGroupLaw κ sB)
    (F : SchemeHomOver sB sB)
    (hF : ∀ (v : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) sB)
        (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) sB)
        (_ : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ v.1 = x.1),
      NeronModelInfra.schemeHomOverComp v F =
        NeronModelInfra.schemeHomOverComp
          (⟨Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫ x.1,
            by rw [Category.assoc, x.2, Category.comp_id]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) sB) F) :

    let tBB : pullback sB sB ⟶ Spec (CommRingCat.of κ) := pullback.fst sB sB ≫ sB
    let xBB : SchemeHomOver tBB sB := ⟨pullback.fst sB sB, rfl⟩
    let yBB : SchemeHomOver tBB sB := ⟨pullback.snd sB sB, pullback.condition.symm⟩
    let m₀ := L.mul tBB xBB (NeronModelInfra.schemeHomOverComp yBB F)
    let m₁ := L.mul tBB (NeronModelInfra.schemeHomOverComp xBB F) yBB
    let Mx : pullback sB sB ⟶ pullback sB sB := pullback.lift m₀.1 m₁.1 (m₀.2.trans m₁.2.symm)
    let eBB : Spec (CommRingCat.of κ) ⟶ pullback sB sB := pullback.lift (L.one (𝟙 _)).1 (L.one (𝟙 _)).1 rfl
    ∀ w : Spec (CommRingCat.of (DualNumber κ)) ⟶ pullback Mx eBB,
      w ≫ pullback.snd Mx eBB = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) →
      w = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ w := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_dualNumber_eq_comp_of_ker_ribetMatrix.solution
