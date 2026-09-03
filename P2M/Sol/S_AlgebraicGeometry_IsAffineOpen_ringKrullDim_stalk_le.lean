import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim Γ(X, U) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x)]
  exact Ideal.height_le_ringKrullDim_of_isPrime
