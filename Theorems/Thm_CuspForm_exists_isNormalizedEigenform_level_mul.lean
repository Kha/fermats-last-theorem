import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isNormalizedEigenform_level_mul
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem CuspForm.exists_isNormalizedEigenform_level_mul {M : ℕ} [NeZero M]
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f.IsNormalizedEigenform)
    {p : ℕ} (hp : p.Prime) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff g n = ModularFormClass.qCoeff f n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isNormalizedEigenform_level_mul.solution
