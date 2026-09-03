import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_fin_eq_of_isClosedImmersion_of_finite_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_fin_eq_of_isClosedImmersion_of_finite_pullback
    {X Y Z : Scheme.{u}} (i₁ : Y ⟶ X) (i₂ : Z ⟶ X) [IsClosedImmersion i₂]
    [Finite ↥(pullback i₁ i₂)] :
    ∃ (n : ℕ) (y : Fin n → Y) (z : Fin n → Z), Function.Injective y ∧
      (∀ r, i₁.base (y r) = i₂.base (z r)) ∧
      ∀ (P : Y) (Q : Z), i₁.base P = i₂.base Q → ∃ r, P = y r ∧ Q = z r := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_fin_eq_of_isClosedImmersion_of_finite_pullback.solution
