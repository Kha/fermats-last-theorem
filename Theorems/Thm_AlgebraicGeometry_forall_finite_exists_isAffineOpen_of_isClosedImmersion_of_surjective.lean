import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_forall_finite_exists_isAffineOpen_of_isClosedImmersion_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.forall_finite_exists_isAffineOpen_of_isClosedImmersion_of_surjective
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f] [Surjective f]
    (hAff : ∀ U : X.Opens, IsAffineOpen (f ⁻¹ᵁ U) → IsAffineOpen U)
    (hZ : ∀ S : Set Z, S.Finite → ∃ U : Z.Opens, IsAffineOpen U ∧ S ⊆ (U : Set Z)) :
    ∀ S : Set X, S.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ (U : Set X) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_forall_finite_exists_isAffineOpen_of_isClosedImmersion_of_surjective.solution
