import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen
    (E : Scheme.{u})
    (U : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Set ↥(Spec (CommRingCat.of R)))
    (hUopen : ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E), IsOpen (U R s))
    (hU : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E),
      U R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (Spec.map (CommRingCat.ofHom ψ)).base ⁻¹' (U R s)) :
    ∃ V : E.Opens,
      (∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E), s.base ⁻¹' (V : Set E) = U R s) ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        Set.range s.base ⊆ (V : Set E) ↔ U R s = Set.univ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen.solution
