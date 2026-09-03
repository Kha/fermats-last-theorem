import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ideal_eq_bot_iff_eq_and_map_and_fg_of_locallyOfFiniteType

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_ideal_eq_bot_iff_eq_and_map_and_fg_of_locallyOfFiniteType
    {Y S : Scheme.{u}} (p : Y ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] :
    ∃ I : ∀ (R : Type u) [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y), σ ≫ p = τ ≫ p → Ideal R,
      (∀ (R : Type u) [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y) (h : σ ≫ p = τ ≫ p),
          I R σ τ h = ⊥ ↔ σ = τ) ∧
      (∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (σ τ : Spec (CommRingCat.of R) ⟶ Y)
          (h : σ ≫ p = τ ≫ p),
        I R' (Spec.map (CommRingCat.ofHom ψ) ≫ σ) (Spec.map (CommRingCat.ofHom ψ) ≫ τ)
            (by rw [Category.assoc, Category.assoc, h]) = (I R σ τ h).map ψ) ∧
      (∀ (R : Type u) [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y) (h : σ ≫ p = τ ≫ p), (I R σ τ h).FG) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ideal_eq_bot_iff_eq_and_map_and_fg_of_locallyOfFiniteType.solution
