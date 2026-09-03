import Mathlib
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_LevelRelabelling
import P2M.Util
import P2M.Sol.S_ModularCurve_isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one
attribute [-simp] WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

theorem ModularCurve.isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓκ : (ℓ : κ) ≠ 0) (hmem : ℓ ∈ M'.primeFactors)
    (W : WeierstrassCurve κ) (hΔ : IsUnit W.Δ)
    (h : ↥M'.primeFactors → Polynomial κ) (hh : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (h p))
    (xG yG : κ) (hG : W.toAffine.Equation xG yG) (hroot : (h ⟨ℓ, hmem⟩).eval xG = 0)
    (b : ℕ) (hb : ¬ ℓ ∣ b)
    (D : ModularCurve.LevelPData κ) (hDP : W.toAffine.Equation D.xP D.yP)
    (hDQ : D.xQ = D.xP ∧ D.yQ = D.yP)
    (hPG : ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) D.xP D.yP =
      (b * ℓ ^ (M'.factorization ℓ - 1)) • ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) xG yG) :
    ModularCurve.IsGamma1Point W ℓ D ∧
      h ⟨ℓ, hmem⟩ ∣ ModularCurve.inLineMulPoly W ℓ (ℓ ^ (M'.factorization ℓ - 1)) D.xP := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot.solution
