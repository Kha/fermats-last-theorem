import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_exists_iso_comp_eq_and_comp_hom_eq_mul

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.exists_iso_comp_eq_and_comp_hom_eq_mul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    ∃ τ : A ≅ A,
      τ.hom ≫ f = f ∧
      ∀ {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        x.1 ≫ τ.hom = (G.mul t x (schemeHomOverComp t (Category.comp_id t) P)).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_iso_comp_eq_and_comp_hom_eq_mul.solution
