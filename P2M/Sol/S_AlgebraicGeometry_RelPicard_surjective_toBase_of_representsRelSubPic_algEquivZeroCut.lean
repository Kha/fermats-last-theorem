import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_surjective_toBase_of_representsRelSubPic_algEquivZeroCut

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) :
    Surjective D.toBase := by
  refine ⟨fun s => ⟨D.zeroSection.base s, ?_⟩⟩
  have hs := congrArg (fun φ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) => φ.base s) D.zeroSection_toBase
  simpa using hs
