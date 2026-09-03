import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_qCoeff_eq_ite_dvd_of_prime

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_qCoeff_eq_ite_dvd_of_prime
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k) (p : ℕ) (hp : p.Prime) :
    ∃ g : CuspForm (Gamma1 (p ^ 2 * N)) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n = if p ∣ n then 0 else ModularFormClass.qCoeff f n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_qCoeff_eq_ite_dvd_of_prime.solution
