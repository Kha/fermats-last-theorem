import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two
set_option autoImplicit false
open ModularCurve
theorem ModularCurve.exists_tangentSlope_nonToricPoint_of_eq_three
    (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (hp3 : p = 3)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ) (k : ℕ) (h1k : 1 ≤ k) (hkp : k ≤ p / 2) :
    IsUnit (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
        + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃) ∧
    ∃ ℓ : LaurentSeries K,
      ℓ * (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
          + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃)
        = 3 * (nonToricPoint K p (ζ ^ (b * k)) k).1 ^ 2
          + 2 * (tateBase K p).a₂ * (nonToricPoint K p (ζ ^ (b * k)) k).1
          + (tateBase K p).a₄ - (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).2 ∧
      ℓ ^ 2 + (tateBase K p).a₁ * ℓ - (tateBase K p).a₂
          - 2 * (nonToricPoint K p (ζ ^ (b * k)) k).1
        = (nonToricPoint K p (ζ ^ (b * k)) k).1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.solution
