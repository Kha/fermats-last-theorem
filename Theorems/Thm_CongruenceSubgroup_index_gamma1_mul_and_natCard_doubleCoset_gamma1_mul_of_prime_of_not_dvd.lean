import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) :
    (CongruenceSubgroup.Gamma1 (M * p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      (p ^ 2 - 1) * (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
    Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 (M * p) : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) =
      2 * (p - 1) * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd.solution
