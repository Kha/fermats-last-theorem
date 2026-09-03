import Mathlib
import Definitions.Def_CyclotomicUniv_Base
import Definitions.Def_ModularCurve_TateVeluRing
import P2M.Util
import P2M.Sol.S_ModularCurve_variableChange_veluQuotient_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_veluXR_tateToricPoint_eq
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

open WeierstrassCurve CyclotomicUniv ModularCurve.TateVeluRing open ModularCurve hiding exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul vcXInv_veluX_and_vcYInv_veluY_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_pow

open scoped Classical in

theorem ModularCurve.variableChange_veluQuotient_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_veluXR_tateToricPoint_eq
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓN : ℓ ∣ N) (m : ℕ) [NeZero m]
    (C : WeierstrassCurve.VariableChange (LaurentSeries (CyclotomicUniv.base N)))
    (hu : (C.u : LaurentSeries (CyclotomicUniv.base N)) = (ℓ : LaurentSeries (CyclotomicUniv.base N)))
    (hr : C.r = HahnSeries.C (CyclotomicUniv.invNat N ℓ hℓN * (((ℓ ^ 2 - 1) * ℓ / 12 : ℕ) : CyclotomicUniv.base N)))
    (hs : C.s = HahnSeries.C (((ℓ - 1) / 2 : ℕ) : CyclotomicUniv.base N))
    (ht : C.t = HahnSeries.C (-(CyclotomicUniv.invNat N ℓ hℓN *
      (((ℓ ^ 2 - 1) * ℓ / 24 : ℕ) : CyclotomicUniv.base N)))) :
    C • ((tateLaurent (CyclotomicUniv.base N)).map (qExpand (CyclotomicUniv.base N) m)).veluQuotient
        ((Finset.Icc 1 (ℓ / 2)).image fun k =>
          tateToricPoint (CyclotomicUniv.base N) m ((CyclotomicUniv.ζUnit N ^ (N / ℓ)) ^ k)) =
      (tateLaurent (CyclotomicUniv.base N)).map (qExpand (CyclotomicUniv.base N) (m * ℓ)) ∧
    ∀ n : ℕ, ¬ N ∣ n * ℓ →
      ModularCurve.TateVeluRing.vcXInvR C
          (ModularCurve.TateVeluRing.veluXR ((tateLaurent (CyclotomicUniv.base N)).map (qExpand (CyclotomicUniv.base N) m))
            ((Finset.Icc 1 (ℓ / 2)).image fun k =>
              tateToricPoint (CyclotomicUniv.base N) m ((CyclotomicUniv.ζUnit N ^ (N / ℓ)) ^ k))
            (tateToricPoint (CyclotomicUniv.base N) m (CyclotomicUniv.ζUnit N ^ n)).1) =
        (tateToricPoint (CyclotomicUniv.base N) (m * ℓ) ((CyclotomicUniv.ζUnit N ^ n) ^ ℓ)).1 ∧
      ModularCurve.TateVeluRing.vcYInvR C
          (ModularCurve.TateVeluRing.veluXR ((tateLaurent (CyclotomicUniv.base N)).map (qExpand (CyclotomicUniv.base N) m))
            ((Finset.Icc 1 (ℓ / 2)).image fun k =>
              tateToricPoint (CyclotomicUniv.base N) m ((CyclotomicUniv.ζUnit N ^ (N / ℓ)) ^ k))
            (tateToricPoint (CyclotomicUniv.base N) m (CyclotomicUniv.ζUnit N ^ n)).1)
          (ModularCurve.TateVeluRing.veluYR ((tateLaurent (CyclotomicUniv.base N)).map (qExpand (CyclotomicUniv.base N) m))
            ((Finset.Icc 1 (ℓ / 2)).image fun k =>
              tateToricPoint (CyclotomicUniv.base N) m ((CyclotomicUniv.ζUnit N ^ (N / ℓ)) ^ k))
            (tateToricPoint (CyclotomicUniv.base N) m (CyclotomicUniv.ζUnit N ^ n)).1
            (tateToricPoint (CyclotomicUniv.base N) m (CyclotomicUniv.ζUnit N ^ n)).2) =
        (tateToricPoint (CyclotomicUniv.base N) (m * ℓ) ((CyclotomicUniv.ζUnit N ^ n) ^ ℓ)).2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_variableChange_veluQuotient_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_veluXR_tateToricPoint_eq.solution
