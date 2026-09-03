import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_isFinite_of_section_of_forall_isAlgClosed_hom_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isIso_of_isFinite_of_section_of_forall_isAlgClosed_hom_eq
    {R : Type u} [CommRing R] {K : Scheme.{u}} (p : K ⟶ Spec (CommRingCat.of R)) [IsFinite p]
    (σ : Spec (CommRingCat.of R) ⟶ K) (hσ : σ ≫ p = 𝟙 _)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (T : Type u) [CommRing T]
      (t' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of k))
      (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (a b : Spec (CommRingCat.of T) ⟶ K), a ≫ p = t' ≫ φ → b ≫ p = t' ≫ φ → a = b) :
    IsIso p := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isFinite_of_section_of_forall_isAlgClosed_hom_eq.solution
