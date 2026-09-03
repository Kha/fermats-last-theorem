import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul

set_option autoImplicit false

open scoped ModularForm MatrixGroups

theorem CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(CuspForm.heckeULinH k q f)) n = ModularFormClass.qCoeff (⇑f) (n * q) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul.solution
