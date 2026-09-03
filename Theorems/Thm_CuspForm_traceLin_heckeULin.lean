import Mathlib
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_traceLin_heckeULin
attribute [-simp] ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply

theorem CuspForm.traceLin_heckeULin {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) (hℓR : ℓ ∣ A.R) (hne : ℓ ≠ q) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    haveI : NeZero A.R := ⟨A.R_pos.ne'⟩
    CuspForm.traceLin A hq (CuspForm.heckeULin 2 hℓM f) = CuspForm.heckeULin 2 hℓR (CuspForm.traceLin A hq f) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_traceLin_heckeULin.solution
