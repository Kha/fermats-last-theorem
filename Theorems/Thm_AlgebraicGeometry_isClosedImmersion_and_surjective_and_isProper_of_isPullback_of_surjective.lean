import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective
    {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i) :
    IsClosedImmersion g ∧ Surjective g ∧ (IsSeparated f₀ → IsSeparated f) ∧
      (UniversallyClosed f₀ → UniversallyClosed f) ∧
      (IsProper f₀ → LocallyOfFiniteType f → IsProper f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective.solution
