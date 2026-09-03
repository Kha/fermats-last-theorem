import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.mem_range_binaryFormRepSL_T_zpow_sub_one {K : Type*} [Field K] [CharZero K] (n : ℕ) {h : ℤ}
    (hh : h ≠ 0) (P : ↥(HeckeEis.BinaryForm K n))
    (hP : MvPolynomial.coeff (Finsupp.single 1 n) (P : MvPolynomial (Fin 2) K) = 0) :
    P ∈ LinearMap.range (HeckeEis.binaryFormRepSL K n (ModularGroup.T ^ h) - 1) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one.solution
