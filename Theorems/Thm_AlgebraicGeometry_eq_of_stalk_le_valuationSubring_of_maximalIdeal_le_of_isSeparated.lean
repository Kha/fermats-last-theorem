import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated
    {X : Scheme.{0}} [IsIntegral X] [X.IsSeparated]
    (𝒪v : ValuationSubring X.functionField) (x₁ x₂ : X)
    (h₁ : ∀ g : X.presheaf.stalk x₁, algebraMap (X.presheaf.stalk x₁) X.functionField g ∈ 𝒪v)
    (h₁' : ∀ g : X.presheaf.stalk x₁, g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x₁) →
      algebraMap (X.presheaf.stalk x₁) X.functionField g ∈ 𝒪v.nonunits)
    (h₂ : ∀ g : X.presheaf.stalk x₂, algebraMap (X.presheaf.stalk x₂) X.functionField g ∈ 𝒪v)
    (h₂' : ∀ g : X.presheaf.stalk x₂, g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x₂) →
      algebraMap (X.presheaf.stalk x₂) X.functionField g ∈ 𝒪v.nonunits) :
    x₁ = x₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated.solution
