import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_index_gamma1_mul_eq_of_prime_of_not_dvd

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.index_gamma1_mul_eq_of_prime_of_not_dvd
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) :
    (CongruenceSubgroup.Gamma1 (M * p)).index = (p ^ 2 - 1) * (CongruenceSubgroup.Gamma1 M).index := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_index_gamma1_mul_eq_of_prime_of_not_dvd.solution
