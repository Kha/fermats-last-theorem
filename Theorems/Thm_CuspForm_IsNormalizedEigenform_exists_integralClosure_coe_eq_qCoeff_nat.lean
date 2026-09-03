import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_exists_integralClosure_coe_eq_qCoeff_nat
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff_nat {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) (n : ℕ) : ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_exists_integralClosure_coe_eq_qCoeff_nat.solution
