import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_and_comp_hom_eq_mul

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_and_comp_hom_eq_mul
    (R : Type u) [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f)
    (d : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    ∃ τ : A ≅ A, τ.hom ≫ f = f ∧ τ.inv ≫ f = f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : NeronModelInfra.SchemeHomOver t f),
        x.1 ≫ τ.hom = (L.mul t x (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) d)).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : NeronModelInfra.SchemeHomOver t f),
        x.1 ≫ τ.inv = (L.mul t x (L.inv t (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) d))).1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_and_comp_hom_eq_mul.solution
