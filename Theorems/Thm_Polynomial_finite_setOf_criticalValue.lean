import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_finite_setOf_criticalValue

set_option autoImplicit false

open Polynomial

universe u

theorem Polynomial.finite_setOf_criticalValue
    {k : Type u} [Field k] (P : k[X]) (hP : derivative P ≠ 0) :
    {c : k | ∃ x : k, P.eval x = c ∧ (derivative P).eval x = 0}.Finite := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_finite_setOf_criticalValue.solution
