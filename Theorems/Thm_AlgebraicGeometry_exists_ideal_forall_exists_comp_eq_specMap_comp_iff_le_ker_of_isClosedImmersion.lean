import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion
    {R : Type u} [CommRing R] {X Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι]
    (y : Spec (CommRingCat.of R) ⟶ X) :
    ∃ J : Ideal R, ∀ (R' : Type u) [CommRing R'] (ψ : R →+* R'),
      (∃ z : Spec (CommRingCat.of R') ⟶ Z, z ≫ ι = Spec.map (CommRingCat.ofHom ψ) ≫ y) ↔ J ≤ RingHom.ker ψ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion.solution
