import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_atkinLehnerLin_heckeULin

theorem CuspForm.atkinLehnerLin_heckeULin {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) (hne : ℓ ≠ q) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    CuspForm.atkinLehnerLin A 2 (CuspForm.heckeULin 2 hℓM f) = CuspForm.heckeULin 2 hℓM (CuspForm.atkinLehnerLin A 2 f) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_atkinLehnerLin_heckeULin.solution
