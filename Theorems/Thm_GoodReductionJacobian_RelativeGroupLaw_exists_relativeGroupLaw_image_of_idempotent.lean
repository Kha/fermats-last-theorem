import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Mathlib
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_idempotent

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_idempotent
    {R : Type u} [CommRing R] {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    [IsSeparated g] [IsAffineHom g] [Flat g] [LocallyOfFiniteType g]
    (e : SchemeHomOver g g)
    (he_hom : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) e =
        L.mul s (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e))
    (he_idem : e.1 ≫ e.1 = e.1) :
    ∃ (E : Scheme.{u}) (i : E ⟶ A) (LE : RelativeGroupLaw R (i ≫ g)),
      IsClosedImmersion i ∧ IsAffineHom (i ≫ g) ∧ Flat (i ≫ g) ∧ LocallyOfFiniteType (i ≫ g) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ g)),
        LE.mul t x y = LE.mul t y x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ g)),
        NeronModelInfra.schemeHomOverComp (LE.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨i, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp x e = x ↔
          ∃ y : SchemeHomOver t (i ≫ g), NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩ = x) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_idempotent.solution
