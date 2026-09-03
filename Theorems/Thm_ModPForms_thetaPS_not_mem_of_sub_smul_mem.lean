import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_SwdAlgebra
import P2M.Util
import P2M.Sol.S_ModPForms_thetaPS_not_mem_of_sub_smul_mem
set_option autoImplicit false

theorem ModPForms.thetaPS_not_mem_of_sub_smul_mem (p : ℕ) (F : Type) [Field F] [CharP F p]
    (M : ℤ → Submodule F (PowerSeries F)) (k : ℤ) (hpk : ¬ (p : ℤ) ∣ k) (φ : PowerSeries F)
    (hserre : (12 : F) • ModPForms.thetaPS φ - (k : F) • (SwdAlgebra.qP F * φ) ∈ M (k + 2))
    (hkatz : SwdAlgebra.qP F * φ ∈ M (k + 2) → φ ∈ M (k - ((p : ℤ) - 1)))
    (hlow : φ ∉ M (k - ((p : ℤ) - 1))) :
    ModPForms.thetaPS φ ∉ M (k + 2) := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_thetaPS_not_mem_of_sub_smul_mem.solution
