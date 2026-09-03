import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularCurve_index_le_relfinrank_qExpFunctionFieldC_gamma0_gammaH_of_charZero
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem ModularCurve.index_le_relfinrank_qExpFunctionFieldC_gamma0_gammaH_of_charZero
    (K : Type*) [Field K] [CharZero K] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index ≤
      (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)).relfinrank
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_index_le_relfinrank_qExpFunctionFieldC_gamma0_gammaH_of_charZero.solution
