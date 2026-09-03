import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import P2M.Util
import P2M.Sol.S_CuspForm_sq_eq_one_of_atkinLehnerLin_eq_smul

theorem CuspForm.sq_eq_one_of_atkinLehnerLin_eq_smul {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f ≠ 0)
    {lam : ℂ} (hlam : CuspForm.atkinLehnerLin W 2 f = lam • f) : lam ^ 2 = 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_sq_eq_one_of_atkinLehnerLin_eq_smul.solution
