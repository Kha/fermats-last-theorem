import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
      (maximalIdeal (Y.presheaf.stalk (g.base x))).map (g.stalkMap x).hom) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero.solution
