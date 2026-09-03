import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_forall_exists_units_smul_conj_mem_of_int_trd_nrd

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_forall_exists_units_smul_conj_mem_of_int_trd_nrd
    {a b : ℚ} (ha : a < 0) (hb : b < 0)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ α : ℍ[ℚ, a, b],
      (∃ t n : ℤ, QuaternionAlgebra.trd α = t ∧ QuaternionAlgebra.nrd α = n) →
      ∃ μ : (ℍ[ℚ, a, b])ˣ, (d : ℚ) • ((μ : ℍ[ℚ, a, b]) * α * ↑μ⁻¹) ∈ O := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_forall_exists_units_smul_conj_mem_of_int_trd_nrd.solution
