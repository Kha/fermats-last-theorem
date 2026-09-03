import Mathlib
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_inLineMulPoly_eq_C_mul_of_toPoint_eq_zsmul_of_eval_prePsi_eq_zero
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂
attribute [-simp] Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_inLineMulPoly_eq_C_mul_of_toPoint_eq_zsmul_of_eval_prePsi_eq_zero
    (T : Type) [Field T] [DecidableEq T] (W : WeierstrassCurve T)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓT : ((ℓ : ℕ) : T) ≠ 0) (hΔ : W.Δ ≠ 0)
    (x y : T) (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0)
    (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
    (x' y' : T) (hxy' : W.toAffine.Equation x' y')
    (hP : ModularCurve.LevelRelabelling.toPoint (W.baseChange T) x' y' =
      a • ModularCurve.LevelRelabelling.toPoint (W.baseChange T) x y)
    (n : ℕ) :
    ∃ u : T, u ≠ 0 ∧ ModularCurve.inLineMulPoly W ℓ n x' = Polynomial.C u * ModularCurve.inLineMulPoly W ℓ n x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_inLineMulPoly_eq_C_mul_of_toPoint_eq_zsmul_of_eval_prePsi_eq_zero.solution
