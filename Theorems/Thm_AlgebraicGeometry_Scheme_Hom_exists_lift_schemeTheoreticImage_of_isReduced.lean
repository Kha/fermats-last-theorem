import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Hom.exists_lift_schemeTheoreticImage_of_isReduced
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (u : T ⟶ Y) [IsReduced T]
    (h : Set.range u.base ⊆ closure (Set.range f.base)) :
    ∃ v : T ⟶ f.image, v ≫ f.imageι = u := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isReduced.solution
