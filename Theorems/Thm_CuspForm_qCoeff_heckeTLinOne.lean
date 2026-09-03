import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_heckeTLinOne

theorem CuspForm.qCoeff_heckeTLinOne {M : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeTLinOne k hp hpM f) n =
      ModularFormClass.qCoeff f (p * n) +
        (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff (CuspForm.diamondLinOne M k p f) (n / p) else 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_heckeTLinOne.solution
