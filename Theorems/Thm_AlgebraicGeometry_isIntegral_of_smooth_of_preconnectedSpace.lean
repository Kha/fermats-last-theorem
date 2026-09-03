import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] [PreconnectedSpace X] [Nonempty X] : IsIntegral X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace.solution
