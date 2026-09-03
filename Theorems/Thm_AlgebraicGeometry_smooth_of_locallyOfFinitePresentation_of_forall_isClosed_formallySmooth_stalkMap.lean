import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [JacobsonSpace ↑X]
    (h : ∀ x : ↑X, IsClosed ({x} : Set ↑X) → (f.stalkMap x).hom.FormallySmooth) :
    Smooth f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap.solution
