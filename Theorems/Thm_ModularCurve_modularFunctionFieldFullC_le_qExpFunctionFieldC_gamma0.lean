import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
    (K : Type*) [Field K] (M : ℕ) [NeZero M] :
    ModularCurve.modularFunctionFieldFullC K M ≤
      ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0.solution
