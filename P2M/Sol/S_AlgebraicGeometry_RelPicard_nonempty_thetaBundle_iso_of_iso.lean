import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_iso_of_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (e : M.L ≅ M'.L) (r n : ℕ) :
    Nonempty (thetaBundle c ε t M r n ≅ thetaBundle c ε t M' r n) := by

  let i1 : M.L ⊗ sectionTwist c ε t r ≅ M'.L ⊗ sectionTwist c ε t r := whiskerRightIso e _
  let i2 := (Scheme.Modules.pushforward (pullback.snd c t)).mapIso i1
  let i3 := (Scheme.Modules.exteriorPower T n).mapIso i2
  exact ⟨(MonoidalClosed.internalHom.mapIso i3.symm.op).app (𝟙_ T.Modules)⟩
