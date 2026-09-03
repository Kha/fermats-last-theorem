import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot
    (E : Scheme.{u})
    (I : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Ideal R)
    (hI : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E),
      I R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (I R s).map ψ) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ E), IsClosedImmersion ι ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        (∃ z : Spec (CommRingCat.of R) ⟶ Z, z ≫ ι = s) ↔ I R s = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.solution
