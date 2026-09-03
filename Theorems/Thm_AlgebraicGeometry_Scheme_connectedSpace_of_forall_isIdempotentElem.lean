import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_connectedSpace_of_forall_isIdempotentElem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.connectedSpace_of_forall_isIdempotentElem
    (X : Scheme.{u}) [Nonempty X]
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) :
    ConnectedSpace X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_connectedSpace_of_forall_isIdempotentElem.solution
