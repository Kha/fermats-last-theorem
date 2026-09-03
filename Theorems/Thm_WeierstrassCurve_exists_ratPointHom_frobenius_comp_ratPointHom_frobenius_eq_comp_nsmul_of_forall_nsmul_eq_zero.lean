import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_RatPointHom
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

theorem WeierstrassCurve.exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (W : WeierstrassCurve κ) [W.IsElliptic] (hss : ∀ P : W.toAffine.Point, p • P = 0 → P = 0) :
    ∃ (ε : ((W.map (frobenius κ p)).map (frobenius κ p)).toAffine.Point →+ W.toAffine.Point)
      (ε' : W.toAffine.Point →+ ((W.map (frobenius κ p)).map (frobenius κ p)).toAffine.Point),
      ε ∈ WeierstrassCurve.rationalHomSet κ ((W.map (frobenius κ p)).map (frobenius κ p)) W ∧
      ε' ∈ WeierstrassCurve.rationalHomSet κ W ((W.map (frobenius κ p)).map (frobenius κ p)) ∧
      ε.comp ε' = AddMonoidHom.id _ ∧ ε'.comp ε = AddMonoidHom.id _ ∧
      (p : ℕ) • AddMonoidHom.id W.toAffine.Point =
        ε.comp ((WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W.map (frobenius κ p))).comp
          (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W))) ∧
      (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W.map (frobenius κ p))).comp
          (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W)) =
        ε'.comp ((p : ℕ) • AddMonoidHom.id W.toAffine.Point) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero.solution
