import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate

theorem Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero
    {K : Type*} [Field K] [IsAlgClosed K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (H : K[X][Y]) {B : ℝ} (hB : ∀ j, (H.coeff j).gaussNorm v 1 ≤ B)
    {y w : K} (hy : v y ≤ 1) (hH : H.evalEval y w = 0)
    (hlt : B * v w < (H.eval 0).gaussNorm v 1) :
    ∃ a ∈ (H.eval 0).roots, v a ≤ 1 ∧
      (H.eval 0).gaussNorm v 1 * v (y - a) ^ (H.eval 0).natDegree ≤ B * v w := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero.solution
