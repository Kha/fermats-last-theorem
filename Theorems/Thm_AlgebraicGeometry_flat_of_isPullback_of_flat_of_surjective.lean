import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_of_isPullback_of_flat_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.flat_of_isPullback_of_flat_of_surjective
    {X Y Y' X' : Scheme.{u}} (ψ : X ⟶ Y) (g : Y' ⟶ Y) [Flat g] [Surjective g] [LocallyOfFinitePresentation g]
    (ψ' : X' ⟶ Y') (π : X' ⟶ X) (h : IsPullback π ψ' ψ g) [Flat ψ'] : Flat ψ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_of_isPullback_of_flat_of_surjective.solution
