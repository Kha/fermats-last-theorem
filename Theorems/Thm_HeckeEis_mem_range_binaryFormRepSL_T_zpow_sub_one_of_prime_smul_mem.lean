import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem (n : ℕ) {p : ℕ} (hp : p.Prime) (hn : n < p)
    {h : ℤ} (hph : ¬ (p : ℤ) ∣ h) (v : ↥(HeckeEis.BinaryForm ℤ n))
    (hv : (p : ℤ) • v ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1)) :
    v ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem.solution
