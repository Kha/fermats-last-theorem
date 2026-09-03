import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le

set_option autoImplicit false

open Polynomial

theorem Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le {K : Type*} [Field K]
    [IsAlgClosed K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : K[X])
    {z : K} (hz : v z ≤ 1) (hlt : v (p.eval z) < p.gaussNorm v 1) :
    ∃ a ∈ p.roots, v a ≤ 1 ∧ p.gaussNorm v 1 * v (z - a) ^ p.natDegree ≤ v (p.eval z) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le.solution
