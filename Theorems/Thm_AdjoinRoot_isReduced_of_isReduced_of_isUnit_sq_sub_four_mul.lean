import Mathlib
import P2M.Util
import P2M.Sol.S_AdjoinRoot_isReduced_of_isReduced_of_isUnit_sq_sub_four_mul

set_option autoImplicit false

open Polynomial

theorem AdjoinRoot.isReduced_of_isReduced_of_isUnit_sq_sub_four_mul
    {R : Type*} [CommRing R] [IsReduced R] (t n : R) (h : IsUnit (t ^ 2 - 4 * n)) :
    IsReduced (AdjoinRoot (X ^ 2 - C t * X + C n : R[X])) := by p2m_exact_reverting @_root_.P2MW.S_AdjoinRoot_isReduced_of_isReduced_of_isUnit_sq_sub_four_mul.solution
