import Definitions.Def_FLTPrelim_ModularRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isResiduallyModularOfLevel_of_dvd
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem WeierstrassCurve.isResiduallyModularOfLevel_of_dvd (W : WeierstrassCurve ℤ) (p : ℕ) {M N : ℕ} [NeZero N] (hMN : M ∣ N) (h : W.IsResiduallyModularOfLevel p M) : W.IsResiduallyModularOfLevel p N := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_of_dvd.solution
