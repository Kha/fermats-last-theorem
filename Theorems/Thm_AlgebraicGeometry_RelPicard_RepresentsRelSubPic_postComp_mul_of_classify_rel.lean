import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_mul_of_classify_rel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_mul_of_classify_rel
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {P : SubPicGroupCondition c ε} {P' : SubPicGroupCondition c' ε'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) (h' : RepresentsRelSubPic c' ε' P'.toSubPicCondition D')
    (θ : SchemeHomOver D.toBase D'.toBase)
    (Rel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c ε t → RigidifiedLineBundle c' ε' t → Prop)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : P.P t M) (N : RigidifiedLineBundle c' ε' t) (hN : P'.P t N),
      Rel t M N → postComp θ (h.classify t M hM) = h'.classify t N hN)
    (htotal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t), P.P t M →
      ∃ N : RigidifiedLineBundle c' ε' t, P'.P t N ∧ Rel t M N)
    (htensor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M₁ M₂ : RigidifiedLineBundle c ε t) (N₁ N₂ : RigidifiedLineBundle c' ε' t),
      Rel t M₁ N₁ → Rel t M₂ N₂ → Rel t (M₁.tensor M₂) (N₁.tensor N₂)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
      postComp θ (h.relativeGroupLaw.mul t x y) = h'.relativeGroupLaw.mul t (postComp θ x) (postComp θ y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_mul_of_classify_rel.solution
