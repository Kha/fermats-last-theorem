import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot_width
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero
attribute [-simp] TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one
attribute [-simp] WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false
open ModularCurve hiding toricPoint_level_mul

theorem ModularCurve.exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot_width
    (F : Type) [Field F] [DecidableEq F] (Λ : Type) [Field Λ] [DecidableEq Λ] [Algebra (LaurentSeries F) Λ]
    (w M' : ℕ) [NeZero w] [NeZero M'] (hM'F : ((M' : ℕ) : F) ≠ 0)
    (ζ : F) (hζ : IsPrimitiveRoot ζ M')
    (C : WeierstrassCurve.VariableChange Λ) :
    ∃ g : (C • (ModularCurve.tateBase F w).baseChange Λ).toAffine.Point,
      (∀ n : ℕ, n • g = 0 ↔ M' ∣ n) ∧
      (∀ n : ℕ, ¬ M' ∣ n →
        ∃ h₁ : ((ModularCurve.tateBase F w).baseChange Λ).toAffine.Nonsingular
            (algebraMap (LaurentSeries F) Λ (ModularCurve.toricPoint F w (ζ ^ n)).1)
            (algebraMap (LaurentSeries F) Λ (ModularCurve.toricPoint F w (ζ ^ n)).2),
          WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F w).baseChange Λ) (n • g) =
            WeierstrassCurve.Affine.Point.some _ _ h₁) ∧
      (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Λ)
          (h₁ : (C • (ModularCurve.tateBase F w).baseChange Λ).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          ((fun p : ↥M'.primeFactors =>
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
          (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
            (Polynomial.X - Polynomial.C (algebraMap (LaurentSeries F) Λ
              (ModularCurve.toricPoint F w ((ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a)).1)))) p).IsRoot x₁) ∧
      (∀ (p : ↥M'.primeFactors) (x₁ : Λ),
        ((fun p : ↥M'.primeFactors =>
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
          (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
            (Polynomial.X - Polynomial.C (algebraMap (LaurentSeries F) Λ
              (ModularCurve.toricPoint F w ((ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a)).1)))) p).IsRoot x₁ ↔
          ∃ (P : (C • (ModularCurve.tateBase F w).baseChange Λ).toAffine.Point) (y₁ : Λ)
            (h₁ : (C • (ModularCurve.tateBase F w).baseChange Λ).toAffine.Nonsingular x₁ y₁),
            P ∈ AddSubgroup.zmultiples g ∧ addOrderOf P = (p : ℕ) ^ M'.factorization (p : ℕ) ∧
            P = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot_width.solution
