import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_forall_geometricPoint_exists_comp_eq_of_flat

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_forall_geometricPoint_exists_comp_eq_of_flat
    {R : Type u} [CommRing R] [IsDomain R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (ι : R →+* Ω) (hι : Function.Injective ι)
    {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [LocallyOfFinitePresentation f]
    [IsReduced X] (i : Z ⟶ Y) [IsClosedImmersion i] (φ : X ⟶ Y)
    (h : ∀ x : Spec (CommRingCat.of Ω) ⟶ X, x ≫ f = Spec.map (CommRingCat.ofHom ι) →
      ∃ z : Spec (CommRingCat.of Ω) ⟶ Z, z ≫ i = x ≫ φ) :
    ∃! ψ : X ⟶ Z, ψ ≫ i = φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_forall_geometricPoint_exists_comp_eq_of_flat.solution
