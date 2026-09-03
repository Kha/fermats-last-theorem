import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul

open scoped Quaternion

theorem QuaternionAlgebra.commute_iff_exists_eq_smul_one_add_smul
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (α : ℍ[ℚ, a, b])
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) (x : ℍ[ℚ, a, b]) :
    x * α = α * x ↔ ∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul.solution
