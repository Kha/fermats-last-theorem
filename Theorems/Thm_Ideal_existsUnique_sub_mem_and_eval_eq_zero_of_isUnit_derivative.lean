import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative

set_option autoImplicit false

open Polynomial

theorem Ideal.existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative
    {W : Type*} [CommRing W] (I : Ideal W) [IsAdicComplete I W]
    (G : Polynomial W) (y₀ : W) (hG : G.eval y₀ ∈ I)
    (hG' : IsUnit ((Polynomial.derivative G).eval y₀)) :
    ∃! y : W, y - y₀ ∈ I ∧ G.eval y = 0 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative.solution
