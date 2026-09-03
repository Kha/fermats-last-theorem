import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

open scoped CategoryTheory.MonObj

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Over (Spec (CommRingCat.of R))} (a b : T ⟶ Over.mk D.toBase) :
    letI := h.grpObj
    Nonempty ((h.poincare.pullbackAlong ⟨(a * b).left, Over.w (a * b)⟩).L ≅
      ((h.poincare.pullbackAlong ⟨a.left, Over.w a⟩).tensor (h.poincare.pullbackAlong ⟨b.left, Over.w b⟩)).L) := by
  letI := h.grpObj
  letI := P.commGroupObj (Opposite.op T)
  have hmul := congrArg Subtype.val (h.homEquiv_mul T a b)
  exact Quotient.exact hmul
