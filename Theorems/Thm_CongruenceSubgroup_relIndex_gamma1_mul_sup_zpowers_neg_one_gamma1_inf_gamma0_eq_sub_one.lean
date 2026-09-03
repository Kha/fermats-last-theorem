import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_relIndex_gamma1_mul_sup_zpowers_neg_one_gamma1_inf_gamma0_eq_sub_one

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.relIndex_gamma1_mul_sup_zpowers_neg_one_gamma1_inf_gamma0_eq_sub_one
    (M p : ℕ) [NeZero M] (hM : 3 ≤ M) [Fact p.Prime] (hpM : ¬ p ∣ M) :
    CongruenceSubgroup.Gamma1 (M * p) ≤ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ∧
    ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ∧
    (∀ γ ∈ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)),
        γ ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ∨
          -γ ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) ∧
    (CongruenceSubgroup.Gamma1 (M * p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).relIndex
        ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) = p - 1 := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_relIndex_gamma1_mul_sup_zpowers_neg_one_gamma1_inf_gamma0_eq_sub_one.solution
