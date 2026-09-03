import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import P2M.Util
import P2M.Sol.S_CuspForm_stableD

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.stableD (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    CuspForm.StableD M H k := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_stableD.solution
