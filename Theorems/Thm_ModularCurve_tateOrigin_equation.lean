module

public import Mathlib
public import Definitions.Def_ModularCurve_TateOrigin
public import Definitions.Def_ModularCurve_TateFormal
public import P2M.Util
public import P2M.Sol.S_ModularCurve_tateOrigin_equation

@[expose] public section
attribute [-instance] ModularCurve.instIsElliptic_tateBase
attribute [-simp] ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero
attribute [-simp] TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.tateOrigin_equation (K : Type*) [CommRing K] :
    tateOriginY K ^ 2 + tateOriginX K * tateOriginY K
      = tateOriginX K ^ 3 + HahnSeries.C (PowerSeries.map (Int.castRingHom K) tateA4) * tateOriginX K
        + HahnSeries.C (PowerSeries.map (Int.castRingHom K) tateA6) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_tateOrigin_equation.solution
