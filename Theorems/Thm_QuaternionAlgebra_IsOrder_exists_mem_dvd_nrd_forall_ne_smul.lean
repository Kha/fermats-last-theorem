import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_mem_dvd_nrd_forall_ne_smul

set_option autoImplicit false
open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_mem_dvd_nrd_forall_ne_smul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (p : ℕ) [Fact p.Prime] :
    ∃ h ∈ Λ, (∀ h' ∈ Λ, h ≠ (p : ℤ) • h') ∧
      ∃ n : ℤ, (n : ℚ) = QuaternionAlgebra.nrd h ∧ (p : ℤ) ∣ n := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_mem_dvd_nrd_forall_ne_smul.solution
