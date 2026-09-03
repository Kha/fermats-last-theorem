import Mathlib
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_traceLin_heckeTLin
attribute [-simp] ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply

theorem CuspForm.traceLin_heckeTLin {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓR : ¬ ℓ ∣ A.R) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    CuspForm.traceLin A hq (CuspForm.heckeTLin 2 hℓ hℓM f) = CuspForm.heckeTLin 2 hℓ hℓR (CuspForm.traceLin A hq f) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_traceLin_heckeTLin.solution
