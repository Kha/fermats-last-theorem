import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CongruenceSubgroup.Gamma_div_le_gamma1_inf_Gamma_sup_zpowers
    (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N) :
    Gamma (N / p) ≤ (Gamma1 N ⊓ Gamma (N / p ^ N.factorization p)) ⊔
      Subgroup.zpowers (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers.solution
