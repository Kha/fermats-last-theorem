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
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_pullback_lift_of_forall_iff_exists_torus
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.SplitTorus ModularCurve ModularCurve.DRLevel

universe u

theorem AlgebraicGeometry.isReduced_pullback_lift_of_forall_iff_exists_torus
    {κ : Type u} [Field κ] [IsAlgClosed κ]
    {G B : Scheme.{u}} (sG : G ⟶ Spec (CommRingCat.of κ)) (sB : B ⟶ Spec (CommRingCat.of κ))
    (LG : RelativeGroupLaw κ sG) (LB : RelativeGroupLaw κ sB) (hsm : Smooth sG) [LocallyOfFiniteType sB]
    (abq : Fin 2 → SchemeHomOver sG sB)

    (habq : ∀ (i : Fin 2) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a b : SchemeHomOver t sG),
      NeronModelInfra.schemeHomOverComp (LG.mul t a b) (abq i) =
        LB.mul t (NeronModelInfra.schemeHomOverComp a (abq i)) (NeronModelInfra.schemeHomOverComp b (abq i)))

    (hsurj : Surjective (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)))

    (r : ℕ) (τ : SchemeHomOver (torusStr κ r) sG) (hτ : IsClosedImmersion τ.1)
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t sG),
      (∀ i, NeronModelInfra.schemeHomOverComp a (abq i) = LB.one t) ↔
        ∃ y : SchemeHomOver t (torusStr κ r), NeronModelInfra.schemeHomOverComp y τ = a)

    (b : Spec (CommRingCat.of κ) ⟶ pullback sB sB) (hb : b ≫ pullback.fst sB sB ≫ sB = 𝟙 _) :
    IsReduced (pullback (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) b) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_pullback_lift_of_forall_iff_exists_torus.solution
