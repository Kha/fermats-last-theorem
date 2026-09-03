import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd
    (q M' : ℕ) [NeZero q] [NeZero M'] (hqM' : Nat.Coprime q M') (ℓ : ℕ) (hℓ : ℓ ∣ M') (d : (ZMod ℓ)ˣ) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ((γ 1 1 : ℤ) : ZMod ℓ) = (d : ZMod ℓ) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd.solution
