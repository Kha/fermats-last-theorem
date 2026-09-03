import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_baseChange_points_mul_poincare_compat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.RelPicard.baseChange_points_mul_poincare_compat
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)) :
    letI := (show RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)).toSubPicCondition (D.baseChange R') from h').grpObj
    ∃ Θ : (Over.mk (𝟙 (Spec (CommRingCat.of R'))) ⟶ Over.mk (D.baseChange R').toBase) ≃
        SchemeHomOver (specMap R R') D.toBase,
      (∀ a, (Θ a).1 = a.left ≫ pullback.fst D.toBase (specMap R R')) ∧
      (∀ a b, Θ (a * b) =
        (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D from h).relativeGroupLaw.mul
          (specMap R R') (Θ a) (Θ b)) ∧
      ∀ a, Nonempty ((h.poincare.pullbackAlong (Θ a)).L ≅
        (Scheme.Modules.pullback (BaseChange.κ c R' (𝟙 (Spec (CommRingCat.of R')))).inv).obj
          (h'.poincare.pullbackAlong
            (⟨a.left, Over.w a⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (D.baseChange R').toBase)).L) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_baseChange_points_mul_poincare_compat.solution
