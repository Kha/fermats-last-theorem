import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClopen_setOf_topologicalKrullDim_preimage_eq_of_smooth_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClopen_setOf_topologicalKrullDim_preimage_eq_of_smooth_of_isProper
    {X S : Scheme.{0}} (f : X ⟶ S) (hs : Smooth f) (hp : IsProper f) (d : ℕ) :
    IsClopen {s : ↥S | topologicalKrullDim ↥(f.base ⁻¹' {s}) = d} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClopen_setOf_topologicalKrullDim_preimage_eq_of_smooth_of_isProper.solution
