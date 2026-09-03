import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_of_smooth_of_field

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
theorem AlgebraicGeometry.isReduced_of_smooth_of_field
    {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [Smooth sX] :
    IsReduced X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_smooth_of_field.solution
