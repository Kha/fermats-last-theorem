import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_of_smooth_over_field

universe u

open AlgebraicGeometry

theorem AlgebraicGeometry.isReduced_of_smooth_over_field {k : Type u} [Field k]
    {Z : Scheme.{u}} {g : Z ⟶ Spec (.of k)} (hg : Smooth g) : IsReduced Z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_smooth_over_field.solution
