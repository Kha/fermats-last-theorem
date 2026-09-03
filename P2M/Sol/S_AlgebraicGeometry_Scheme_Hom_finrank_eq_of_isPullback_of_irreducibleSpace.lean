import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_eq_of_isPullback_of_irreducibleSpace

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] [IrreducibleSpace Y]
    (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (h : IsPullback g' π' π g) [Nonempty Y'] (d : ℕ)
    (hd : ∀ y' : Y', π'.finrank y' = d) (y : Y) : π.finrank y = d := by
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y')
  have hlc := Scheme.Hom.isLocallyConstant_finrank π
  have h1 : π.finrank (g y₀) = d := by
    rw [← Scheme.Hom.finrank_of_isPullback g' π' π g h y₀]
    exact hd y₀
  rw [← h1]
  exact hlc.apply_eq_of_preconnectedSpace y (g y₀)
