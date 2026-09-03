import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import P2M.Util
import P2M.Sol.S_CuspForm_atkinLehnerLin_atkinLehnerLin_eq_smul

theorem CuspForm.atkinLehnerLin_atkinLehnerLin_eq_smul {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    CuspForm.atkinLehnerLin W k (CuspForm.atkinLehnerLin W k f) = ((q : ℂ) ^ (k - 2)) • f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_atkinLehnerLin_atkinLehnerLin_eq_smul.solution
