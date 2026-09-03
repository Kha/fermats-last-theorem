import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_IsGamma0PowAt_exists_faithfullyFlat_map_eq_prod_X_sub_C_of_ne_two
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

universe u

theorem ModularCurve.IsGamma0PowAt.exists_faithfullyFlat_map_eq_prod_X_sub_C_of_ne_two
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (p k : ℕ) [Fact p.Prime] (hp : IsUnit ((p : ℕ) : T)) (hp2 : p ≠ 2) (h : Polynomial T)
    (hh : ModularCurve.IsGamma0PowAt W p k h) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra T S) (_ : Module.FaithfullyFlat T S)
      (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (x y : ι → S),
      (∀ i, (W.map (algebraMap T S)).toAffine.Equation (x i) (y i)) ∧
      h.map (algebraMap T S) = ∏ i, (Polynomial.X - Polynomial.C (x i)) ∧
      (∀ i j, i ≠ j → IsUnit (x i - x j)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsGamma0PowAt_exists_faithfullyFlat_map_eq_prod_X_sub_C_of_ne_two.solution
