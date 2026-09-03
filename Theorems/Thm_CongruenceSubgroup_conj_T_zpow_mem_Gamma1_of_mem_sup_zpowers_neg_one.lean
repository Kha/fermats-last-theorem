import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_conj_T_zpow_mem_Gamma1_of_mem_sup_zpowers_neg_one

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.conj_T_zpow_mem_Gamma1_of_mem_sup_zpowers_neg_one (M : ℕ) (hM : ¬ M ∣ 4)
    (σ : SL(2, ℤ)) (h : ℤ) (hmem : σ * ModularGroup.T ^ h * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    σ * ModularGroup.T ^ h * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 M := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_conj_T_zpow_mem_Gamma1_of_mem_sup_zpowers_neg_one.solution
