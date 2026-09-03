import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_heckeAlphaC_jGeomGen_neg_iff_ord_heckeBetaC_jGeomGen_neg
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.ord_heckeAlphaC_jGeomGen_neg_iff_ord_heckeBetaC_jGeomGen_neg
    (K : Type) [Field K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (y : Place K ↥(charLDegeneracyRoof K N ℓ)) :
    y.ord (heckeAlphaC K N ℓ (jGeomGen K N)) < 0 ↔ y.ord (heckeBetaC K N ℓ (jGeomGen K N)) < 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_heckeAlphaC_jGeomGen_neg_iff_ord_heckeBetaC_jGeomGen_neg.solution
