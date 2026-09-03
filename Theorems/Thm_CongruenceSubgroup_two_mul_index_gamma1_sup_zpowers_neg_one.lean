import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_two_mul_index_gamma1_sup_zpowers_neg_one

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.two_mul_index_gamma1_sup_zpowers_neg_one
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    2 * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index = (CongruenceSubgroup.Gamma1 N).index := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_two_mul_index_gamma1_sup_zpowers_neg_one.solution
