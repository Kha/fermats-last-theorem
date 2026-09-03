import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Vandermonde
import P2M.Util
import P2M.Sol.S_Matrix_exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le

set_option autoImplicit false

theorem Matrix.exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le
    (L : ℕ) (x : Fin L → ℂ) (hx : Function.Injective x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (v : Fin L → E) (B : ℝ),
      (∀ t : Fin L, ‖∑ m : Fin L, (x t) ^ (m : ℕ) • v m‖ ≤ B) → ∀ m : Fin L, ‖v m‖ ≤ C * B := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le.solution
