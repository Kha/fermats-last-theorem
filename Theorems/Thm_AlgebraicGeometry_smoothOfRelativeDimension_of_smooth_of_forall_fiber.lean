import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_forall_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (n : ℕ)
    (h : ∀ y : Y, SmoothOfRelativeDimension n (f.fiberToSpecResidueField y)) :
    SmoothOfRelativeDimension n f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber.solution
