import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_translate_eq_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace RP5Sol

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem comp_translate (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    z.1 ≫ L.translate x = (L.mul t z (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) x)).1 := by
  let xf : SchemeHomOver f f := ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩
  have h := L.mul_natural f t z.1 z.2 RelativeGroupLaw.idPoint xf
  have h1 : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (RelativeGroupLaw.idPoint (f := f)) = z :=
    Subtype.ext (Category.comp_id _)
  have h2 : GoodReductionJacobian.schemeHomOverComp z.1 z.2 xf =
      GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) x :=
    Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, xf, ← Category.assoc, z.2])
  have h' := congrArg Subtype.val h
  rw [h1, h2, GoodReductionJacobian.schemeHomOverComp_coe] at h'
  unfold RelativeGroupLaw.translate
  exact h'

end RP5Sol

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    z.1 ≫ L.translate x = (L.mul t z (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) x)).1 :=
  RP5Sol.comp_translate L t z x
