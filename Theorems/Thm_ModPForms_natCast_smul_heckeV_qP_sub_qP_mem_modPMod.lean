import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_SwdAlgebra
import P2M.Util
import P2M.Sol.S_ModPForms_natCast_smul_heckeV_qP_sub_qP_mem_modPMod
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

theorem ModPForms.natCast_smul_heckeV_qP_sub_qP_mem_modPMod (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] :
    (ℓ : F) • PowerSeries.heckeV ℓ (SwdAlgebra.qP F) - SwdAlgebra.qP F ∈ ModPForms.modPMod ℓ 2 F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_natCast_smul_heckeV_qP_sub_qP_mem_modPMod.solution
