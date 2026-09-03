import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_mul_comp_hom_eq_of_iso

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_mul_comp_hom_eq_of_iso
    {R : Type u} [CommRing R] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (e : A ≅ A') (he : e.hom ≫ f' = f) (L : RelativeGroupLaw R f) :
    ∃ L' : RelativeGroupLaw R f',
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (L'.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, he, y.2]⟩).1 =
          (L.mul t x y).1 ≫ e.hom) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (L'.one t).1 = (L.one t).1 ≫ e.hom) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_mul_comp_hom_eq_of_iso.solution
