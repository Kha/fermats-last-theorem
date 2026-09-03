import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsClosedImmersion.exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (ι : Z ⟶ Spec (CommRingCat.of S))
    [IsClosedImmersion ι] [LocallyOfFinitePresentation ι] :
    ∃ J : Ideal S, J.FG ∧ ∀ (R : Type u) [CommRing R] (φ : S →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Z, y ≫ ι = Spec.map (CommRingCat.ofHom φ)) ↔ J.map φ = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot.solution
