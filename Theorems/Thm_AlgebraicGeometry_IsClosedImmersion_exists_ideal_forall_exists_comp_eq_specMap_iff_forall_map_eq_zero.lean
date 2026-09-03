import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsClosedImmersion.exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (ι : Z ⟶ Spec (CommRingCat.of S)) [IsClosedImmersion ι] :
    ∃ J : Ideal S, ∀ (R : Type u) [CommRing R] (φ : S →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Z, y ≫ ι = Spec.map (CommRingCat.ofHom φ)) ↔ ∀ x ∈ J, φ x = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero.solution
