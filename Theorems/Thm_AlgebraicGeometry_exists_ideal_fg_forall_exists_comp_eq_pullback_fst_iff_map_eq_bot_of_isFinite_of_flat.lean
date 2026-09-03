import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ideal_fg_forall_exists_comp_eq_pullback_fst_iff_map_eq_bot_of_isFinite_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.exists_ideal_fg_forall_exists_comp_eq_pullback_fst_iff_map_eq_bot_of_isFinite_of_flat
    (S : Type u) [CommRing S] (C W : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of S))
    [IsFinite c] [Flat c] [LocallyOfFinitePresentation c]
    (w : W ⟶ C) [IsClosedImmersion w] [LocallyOfFinitePresentation w] :
    ∃ J : Ideal S, J.FG ∧ ∀ (T : Type u) [CommRing T] (ψ : S →+* T),
      (∃ ℓ : pullback c (Spec.map (CommRingCat.ofHom ψ)) ⟶ W,
          ℓ ≫ w = pullback.fst c (Spec.map (CommRingCat.ofHom ψ))) ↔ J.map ψ = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ideal_fg_forall_exists_comp_eq_pullback_fst_iff_map_eq_bot_of_isFinite_of_flat.solution
