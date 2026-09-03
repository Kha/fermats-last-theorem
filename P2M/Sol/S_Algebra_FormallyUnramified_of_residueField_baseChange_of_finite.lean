import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite
open scoped TensorProduct

open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem solution (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.FormallyUnramified R S := by
  haveI : Module.Finite S Ω[S⁄R] := inferInstance
  haveI : Module.Finite R Ω[S⁄R] := Module.Finite.trans S _
  have e := KaehlerDifferential.tensorKaehlerEquivBase R (ResidueField R) S
    (ResidueField R ⊗[R] S)
  haveI : Subsingleton Ω[(ResidueField R ⊗[R] S)⁄(ResidueField R)] :=
    h.subsingleton_kaehlerDifferential
  haveI : Subsingleton (ResidueField R ⊗[R] Ω[S⁄R]) := e.toEquiv.subsingleton
  exact ⟨(IsLocalRing.subsingleton_tensorProduct (R := R) (M := Ω[S⁄R])).mp inferInstance⟩
