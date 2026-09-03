import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

open scoped CategoryTheory.MonObj

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    (T : Over (Spec (CommRingCat.of R))) :
    letI := h.grpObj
    Nonempty ((h.poincare.pullbackAlong
        ⟨(1 : T ⟶ Over.mk D.toBase).left, Over.w (1 : T ⟶ Over.mk D.toBase)⟩).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) T.hom).L) := by
  letI := h.grpObj
  letI := P.commGroupObj (Opposite.op T)
  have hone := congrArg Subtype.val (h.homEquiv_one T)
  exact Quotient.exact hone
