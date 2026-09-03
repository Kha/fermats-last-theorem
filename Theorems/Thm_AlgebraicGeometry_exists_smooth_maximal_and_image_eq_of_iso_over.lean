import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_smooth_maximal_and_image_eq_of_iso_over

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u in

theorem AlgebraicGeometry.exists_smooth_maximal_and_image_eq_of_iso_over
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (hdim : ∀ V : X.Opens, Smooth (V.ι ≫ f) → SmoothOfRelativeDimension n (V.ι ≫ f)) :
    ∃ U : X.Opens, SmoothOfRelativeDimension n (U.ι ≫ f) ∧
      (∀ V : X.Opens, Smooth (V.ι ≫ f) → V ≤ U) ∧
      (∀ w : X ≅ X, w.hom ≫ f = f → w.hom ''ᵁ U = U) ∧
      (∀ w : X ≅ X, w.hom ≫ f = f → ∀ (T : Scheme.{u}) (ε : T ⟶ X),
        Set.range ε.base ⊆ (U : Set X) → Set.range (ε ≫ w.hom).base ⊆ (U : Set X)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_smooth_maximal_and_image_eq_of_iso_over.solution
