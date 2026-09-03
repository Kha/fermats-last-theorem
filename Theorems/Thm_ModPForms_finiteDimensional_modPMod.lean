import Mathlib
import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_finiteDimensional_modPMod
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

theorem ModPForms.finiteDimensional_modPMod (N : ℕ) [NeZero N] (k : ℤ) (F : Type) [Field F] :
    FiniteDimensional F ↥(ModPForms.modPMod N k F) := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_finiteDimensional_modPMod.solution
