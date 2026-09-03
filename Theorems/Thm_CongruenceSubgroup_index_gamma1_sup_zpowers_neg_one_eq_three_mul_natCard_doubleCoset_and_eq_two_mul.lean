import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) :
    (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
        3 * Nat.card (DoubleCoset.Quotient
          (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) ∧
      (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
        2 * Nat.card (DoubleCoset.Quotient
          (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
          (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul.solution
