import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsAffineOpen.ringKrullDim_stalk_le
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim Γ(X, U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le.solution
