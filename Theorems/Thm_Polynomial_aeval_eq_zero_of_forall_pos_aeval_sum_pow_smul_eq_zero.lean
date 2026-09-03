import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import P2M.Util
import P2M.Sol.S_Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero

set_option autoImplicit false

theorem Polynomial.aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero
    (R D : ℕ) (N : Fin (D + 1) → Matrix (Fin R) (Fin R) ℂ) (q : Polynomial ℂ)
    (h : ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (D + 1), ((y : ℂ) ^ (a : ℕ)) • N a) q = 0) :
    Polynomial.aeval (N 0) q = 0 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero.solution
