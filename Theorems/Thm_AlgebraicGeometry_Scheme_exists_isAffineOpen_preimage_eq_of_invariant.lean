import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_isAffineOpen_preimage_eq_of_invariant
    {X R Y : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (p : X ⟶ Y) (w : s ≫ p = t ≫ p)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p) (W : X.Opens) (hW : IsAffineOpen W) (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ p ⁻¹ᵁ V = W := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant.solution
