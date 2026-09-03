import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime

set_option autoImplicit false

open CongruenceSubgroup

theorem CuspForm.exists_gamma1_qCoeff_eq_ite_coprime (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm (Gamma1 N) k) (Q : ℕ) (hQ : Q ≠ 0) (M : ℕ) (hM : N * Q ^ 2 ∣ M) :
    ∃ g : CuspForm (Gamma1 M) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if n.Coprime Q then ModularFormClass.qCoeff f n else 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime.solution
