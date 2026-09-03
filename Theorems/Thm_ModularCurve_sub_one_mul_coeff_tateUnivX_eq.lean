import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_sub_one_mul_coeff_tateUnivX_eq
attribute [-simp] TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero

set_option autoImplicit false

theorem ModularCurve.sub_one_mul_coeff_tateUnivX_eq
    (i k : ℕ) :
    (((i : ℤ) - k) ^ 2 - 1) * MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) ModularCurve.tateUnivX =
      6 * MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) (ModularCurve.tateUnivX ^ 2) +
        2 * MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) ModularCurve.tateUnivA4 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sub_one_mul_coeff_tateUnivX_eq.solution
