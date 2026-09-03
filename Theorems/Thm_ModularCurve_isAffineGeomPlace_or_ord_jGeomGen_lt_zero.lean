import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.isAffineGeomPlace_or_ord_jGeomGen_lt_zero
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) :
    IsAffineGeomPlace K N w ∨ w.ord (jGeomGen K N) < 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero.solution
