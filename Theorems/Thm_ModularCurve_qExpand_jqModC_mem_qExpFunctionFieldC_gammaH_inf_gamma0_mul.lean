import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (hNℓ : ((N * ℓ : ℕ) : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (H : Subgroup (ZMod N)ˣ) :
    ModularCurve.qExpand K ℓ (ModularCurve.jqModC K) ∈ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul.solution
