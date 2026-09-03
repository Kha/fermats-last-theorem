import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_heckePS_mem_modPCusp
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

theorem ModPForms.heckePS_mem_modPCusp (N' : ℕ) [NeZero N'] (F : Type) [Field F]
    (k : ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPCusp N' k F) :
    ModPForms.heckePS k ℓ φ ∈ ModPForms.modPCusp N' k F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_heckePS_mem_modPCusp.solution
