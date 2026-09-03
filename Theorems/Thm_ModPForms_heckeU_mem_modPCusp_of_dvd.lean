import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import P2M.Util
import P2M.Sol.S_ModPForms_heckeU_mem_modPCusp_of_dvd
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

theorem ModPForms.heckeU_mem_modPCusp_of_dvd (M : ℕ) [NeZero M] (k : ℤ) (ℓ : ℕ) (hℓM : ℓ ∣ M)
    (F : Type) [Field F] (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPCusp M k F) :
    PowerSeries.heckeU ℓ φ ∈ ModPForms.modPCusp M k F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_heckeU_mem_modPCusp_of_dvd.solution
