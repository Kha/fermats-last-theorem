import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff

set_option autoImplicit false
open scoped MatrixGroups in

theorem CongruenceSubgroup.mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff
    (N : ℕ) (β : SL(2, ℤ)) :
    ((β ∈ CongruenceSubgroup.Gamma1 N ∨ -β ∈ CongruenceSubgroup.Gamma1 N) ↔
        (((β 1 0 : ℤ) : ZMod N) = 0 ∧
          (((β 0 0 : ℤ) : ZMod N) = 1 ∨ ((β 0 0 : ℤ) : ZMod N) = -1))) ∧
    ((∃ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma1 N ∨
        -(β * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∈ CongruenceSubgroup.Gamma1 N) ↔
        (((β 1 0 : ℤ) : ZMod N) = 1 ∨ ((β 1 0 : ℤ) : ZMod N) = -1)) ∧
    (∃ a b : ZMod N, a * ((β 0 0 : ℤ) : ZMod N) + b * ((β 1 0 : ℤ) : ZMod N) = 1) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff.solution
