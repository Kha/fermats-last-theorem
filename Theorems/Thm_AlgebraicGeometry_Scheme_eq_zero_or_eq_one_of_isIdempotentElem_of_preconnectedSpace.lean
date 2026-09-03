import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_eq_zero_or_eq_one_of_isIdempotentElem_of_preconnectedSpace

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.eq_zero_or_eq_one_of_isIdempotentElem_of_preconnectedSpace
    (X : Scheme.{u}) [PreconnectedSpace X] (e : Γ(X, ⊤)) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_eq_zero_or_eq_one_of_isIdempotentElem_of_preconnectedSpace.solution
