import Mathlib
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_traceLin_heckeULin_eq_zero_of_traceLin_eq_zero_of_traceLin_atkinLehnerLin_eq_zero

theorem CuspForm.traceLin_heckeULin_eq_zero_of_traceLin_eq_zero_of_traceLin_atkinLehnerLin_eq_zero {M q : ℕ} [NeZero M]
    (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) (hqM : q ∣ M) {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (h1 : CuspForm.traceLin A hq f = 0) (h2 : CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f) = 0) :
    CuspForm.traceLin A hq (CuspForm.heckeULin 2 hqM f) = 0 ∧
      CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 (CuspForm.heckeULin 2 hqM f)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_traceLin_heckeULin_eq_zero_of_traceLin_eq_zero_of_traceLin_atkinLehnerLin_eq_zero.solution
