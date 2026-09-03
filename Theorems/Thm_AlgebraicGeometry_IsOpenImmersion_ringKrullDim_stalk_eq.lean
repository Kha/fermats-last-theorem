import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq
    {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    ringKrullDim (U.presheaf.stalk u) = ringKrullDim (X.presheaf.stalk (i.base u)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq.solution
