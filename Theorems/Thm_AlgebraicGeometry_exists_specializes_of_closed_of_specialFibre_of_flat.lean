import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_specializes_of_closed_of_specialFibre_of_flat

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.exists_specializes_of_closed_of_specialFibre_of_flat
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]

    (hpos : ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ ∃ y : X₀, η ⤳ y ∧ y ≠ η)
    (x₀ : X₀) (hx₀ : toBase₀.base x₀ = closedPoint A₀) (hcl : ∀ y : X₀, x₀ ⤳ y → y = x₀) :
    ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧ η ⤳ x₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_specializes_of_closed_of_specialFibre_of_flat.solution
