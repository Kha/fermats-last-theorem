import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import P2M.Util
import P2M.Sol.S_CuspForm_atkinLehnerLin_atkinLehnerLin

theorem CuspForm.atkinLehnerLin_atkinLehnerLin {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    CuspForm.atkinLehnerLin W 2 (CuspForm.atkinLehnerLin W 2 f) = f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_atkinLehnerLin_atkinLehnerLin.solution
