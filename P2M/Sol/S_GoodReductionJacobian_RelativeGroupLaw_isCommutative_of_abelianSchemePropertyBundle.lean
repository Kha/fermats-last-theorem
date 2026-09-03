import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_abelianSchemePropertyBundle
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian

namespace CommLambda
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable def op {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) : RelativeGroupLaw R f where
  mul t x y := L.mul t y x
  one t := L.one t
  inv t x := L.inv t x
  mul_assoc t x y z := (L.mul_assoc t z y x).symm
  one_mul t x := L.mul_one t x
  mul_one t x := L.one_mul t x
  inv_mul_cancel t x := L.mul_inv_cancel t x
  mul_natural t t' ψ hψ x y := L.mul_natural t t' ψ hψ y x

theorem op_mul {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    (op L).mul t x y = L.mul t y x := rfl

theorem op_one {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (op L).one t = L.one t := rfl

end CommLambda

theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
    (hJ : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f) :
    L.IsCommutative := by
  intro T t x y
  have h := GoodReductionJacobian.RelativeGroupLaw.mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle R hJ L (CommLambda.op L)
    rfl t x y
  rw [h]
  rfl
