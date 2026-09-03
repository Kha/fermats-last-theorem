import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_SwdAlgebra
import P2M.Util
import P2M.Sol.S_ModPForms_smul_thetaPS_sub_smul_mem_modPMod_add_two
set_option autoImplicit false

theorem ModPForms.smul_thetaPS_sub_smul_mem_modPMod_add_two (N' : ℕ) [NeZero N'] (F : Type) [Field F] (k : ℤ)
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N' k F) :
    (12 : F) • ModPForms.thetaPS φ - (k : F) • (SwdAlgebra.qP F * φ) ∈ ModPForms.modPMod N' (k + 2) F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_smul_thetaPS_sub_smul_mem_modPMod_add_two.solution
