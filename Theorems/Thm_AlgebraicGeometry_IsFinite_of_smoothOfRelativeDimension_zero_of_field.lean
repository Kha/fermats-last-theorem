import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsFinite.of_smoothOfRelativeDimension_zero_of_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 0 f] [QuasiCompact f] : IsFinite f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field.solution
