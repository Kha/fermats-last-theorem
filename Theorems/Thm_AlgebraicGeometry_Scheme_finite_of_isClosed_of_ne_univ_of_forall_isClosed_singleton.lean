import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (hdim : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X)) :
    ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton.solution
