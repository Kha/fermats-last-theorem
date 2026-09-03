import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_Velu
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one
attribute [-simp] TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero

set_option autoImplicit false

open ModularCurve hiding tateUniv_equation exists_variableChange_veluQuotient_toricSlotSet toricPoint_level_mul open WeierstrassCurve

universe u

open scoped Classical in

theorem ModularCurve.exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (m : ℕ) [NeZero m] :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries K),
      (C.u : LaurentSeries K) = (ℓ : LaurentSeries K) ∧
        C.r = HahnSeries.C (((ℓ : K) ^ 2 - 1) / 12) ∧
          C.s = HahnSeries.C (((ℓ : K) - 1) / 2) ∧
            C.t = HahnSeries.C (-(((ℓ : K) ^ 2 - 1) / 24)) ∧
              C • ((tateLaurent K).map (qExpand K m)).veluQuotient
                  ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m (ζ ^ k)) =
                (tateLaurent K).map (qExpand K (m * ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul.solution
