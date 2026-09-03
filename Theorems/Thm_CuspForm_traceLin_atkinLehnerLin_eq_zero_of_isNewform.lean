import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_LevelLoweringTrace
import P2M.Util
import P2M.Sol.S_CuspForm_traceLin_atkinLehnerLin_eq_zero_of_isNewform
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply

theorem CuspForm.traceLin_atkinLehnerLin_eq_zero_of_isNewform {N q : ℕ} [NeZero N]
    (W : ModularForm.AtkinLehnerDatum N q) (hq : q.Prime)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform) :
    CuspForm.traceLin W hq (CuspForm.atkinLehnerLin W 2 f) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_traceLin_atkinLehnerLin_eq_zero_of_isNewform.solution
