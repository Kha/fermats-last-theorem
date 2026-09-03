import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural
    {R : Type u} [CommRing R] {Z Y : Scheme.{u}}
    (fZ : Z ⟶ Spec (CommRingCat.of R)) (fY : Y ⟶ Spec (CommRingCat.of R))

    (η : ∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z),
      z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C)) → (Spec (CommRingCat.of C) ⟶ Y))

    (hη_over : ∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z)
      (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))),
      η C z hz ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap R C)))

    (hη_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C'] (φ : C →ₐ[R] C')
      (z : Spec (CommRingCat.of C) ⟶ Z) (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C)))
      (hz' : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C'))),
      η C' (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z) hz' = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ η C z hz) :
    ∃ u : Z ⟶ Y, u ≫ fY = fZ ∧
      (∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z)
        (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))), z ≫ u = η C z hz) ∧
      ∀ v : Z ⟶ Y,
        (∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z)
          (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))), z ≫ v = η C z hz) → v = u := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural.solution
