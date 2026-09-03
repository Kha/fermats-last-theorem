import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (M' : ℕ) [NeZero M'] (hℓM' : ¬ ℓ ∣ M') :

    (∃ w : SL(2, ℤ), w ∈ CongruenceSubgroup.Gamma q ∧ w ∈ CongruenceSubgroup.Gamma0 M' ∧
      ((w 0 0 : ℤ) : ZMod ℓ) = 0 ∧ ((w 0 1 : ℤ) : ZMod ℓ) = -1 ∧
      ((w 1 0 : ℤ) : ZMod ℓ) = 1 ∧ ((w 1 1 : ℤ) : ZMod ℓ) = 0) ∧

    (∀ w : SL(2, ℤ), w ∈ CongruenceSubgroup.Gamma q → w ∈ CongruenceSubgroup.Gamma0 M' →
      ((w 0 0 : ℤ) : ZMod ℓ) = 0 → ((w 0 1 : ℤ) : ZMod ℓ) = -1 →
      ((w 1 0 : ℤ) : ZMod ℓ) = 1 → ((w 1 1 : ℤ) : ZMod ℓ) = 0 →
      ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∃ l : List (SL(2, ℤ)),
          (∀ e ∈ l, ∃ s : ℤ, (q : ℤ) ∣ s ∧ (e = ModularGroup.T ^ s ∨ e = w * ModularGroup.T ^ s * w⁻¹)) ∧
          γ * (l.prod)⁻¹ ∈ CongruenceSubgroup.Gamma (q * ℓ) ∧
          l.prod ∈ CongruenceSubgroup.Gamma0 M') := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0.solution
