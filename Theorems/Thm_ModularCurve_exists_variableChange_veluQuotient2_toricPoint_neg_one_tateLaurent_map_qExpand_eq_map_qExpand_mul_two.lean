import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_variableChange_veluQuotient2_toricPoint_neg_one_tateLaurent_map_qExpand_eq_map_qExpand_mul_two
attribute [-simp] TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero

set_option autoImplicit false

open ModularCurve WeierstrassCurve

universe u

theorem ModularCurve.exists_variableChange_veluQuotient2_toricPoint_neg_one_tateLaurent_map_qExpand_eq_map_qExpand_mul_two
    (K : Type u) [Field K] [CharZero K] (m : ℕ) [NeZero m] :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries K),
      (C.u : LaurentSeries K) = (2 : LaurentSeries K) ∧
        C.r = HahnSeries.C ((1 : K) / 4) ∧
          C.s = HahnSeries.C ((1 : K) / 2) ∧
            C.t = HahnSeries.C (-((1 : K) / 8)) ∧
              C • ((tateLaurent K).map (qExpand K m)).veluQuotient2 (toricPoint K m (-1)).1 (toricPoint K m (-1)).2 =
                (tateLaurent K).map (qExpand K (m * 2)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_variableChange_veluQuotient2_toricPoint_neg_one_tateLaurent_map_qExpand_eq_map_qExpand_mul_two.solution
