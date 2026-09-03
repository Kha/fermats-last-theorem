import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_AddSubgroup_factorial_nsmul_mem_of_le_of_natCard_le_mul

set_option autoImplicit false

theorem AddSubgroup.factorial_nsmul_mem_of_le_of_natCard_le_mul
    {M : Type*} [AddCommGroup M] (H K : AddSubgroup M) (hHK : H ≤ K) [Finite K]
    (C : ℕ) (hC : Nat.card K ≤ Nat.card H * C) :
    ∀ g ∈ K, (Nat.factorial C) • g ∈ H := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_factorial_nsmul_mem_of_le_of_natCard_le_mul.solution
