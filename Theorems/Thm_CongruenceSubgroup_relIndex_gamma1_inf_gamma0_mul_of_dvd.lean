import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd

set_option autoImplicit false

theorem CongruenceSubgroup.relIndex_gamma1_inf_gamma0_mul_of_dvd (M q : ℕ) [NeZero M] (hq : q ∣ M) :
    (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * q)).relIndex (CongruenceSubgroup.Gamma1 M) = q := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd.solution
