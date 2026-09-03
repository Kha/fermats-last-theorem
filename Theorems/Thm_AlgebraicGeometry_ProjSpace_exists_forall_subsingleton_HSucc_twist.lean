import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist
    {A : Type u} [CommRing A] [IsNoetherianRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsFinite φ]
    (π : X ⟶ Spec (.of A)) (hπ : φ ≫ ProjSpace.π A N = π) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ i : ℕ,
      Subsingleton ((ProjSpace.twist π φ m).HSucc (ProjSpace.stdCoverPullback φ) i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.solution
