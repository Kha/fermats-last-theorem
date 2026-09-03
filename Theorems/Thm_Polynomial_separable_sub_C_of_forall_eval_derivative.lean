import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_separable_sub_C_of_forall_eval_derivative

set_option autoImplicit false

open Polynomial

universe u

theorem Polynomial.separable_sub_C_of_forall_eval_derivative
    {k : Type u} [Field k] [IsAlgClosed k] (P : k[X]) (c : k)
    (hc : ∀ x : k, (derivative P).eval x = 0 → P.eval x ≠ c) :
    (P - C c).Separable := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_separable_sub_C_of_forall_eval_derivative.solution
