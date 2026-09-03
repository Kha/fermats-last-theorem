import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_gamma1_inf_gamma0_eq_gamma1_inf_gamma0_mul_of_coprime

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.gamma1_inf_gamma0_eq_gamma1_inf_gamma0_mul_of_coprime (N ℓ : ℕ) [NeZero N]
    (hNℓ : Nat.Coprime N ℓ) :
    CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 ℓ =
      CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 (N * ℓ) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_gamma1_inf_gamma0_eq_gamma1_inf_gamma0_mul_of_coprime.solution
