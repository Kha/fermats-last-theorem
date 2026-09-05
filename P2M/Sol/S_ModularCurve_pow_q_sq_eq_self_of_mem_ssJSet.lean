module

public import Mathlib
public import Definitions.Def_ModularCurve_SupersingularModuli
public import Theorems.Thm_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

open ModularCurve

set_option autoImplicit false

theorem solution {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] {a : K} (ha : a ∈ ModularCurve.ssJSet q K) : a ^ (q ^ 2) = a := by
  have h := WeierstrassCurve.j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero q (WeierstrassCurve.ofJ a)
    (fun P hP => (mem_ssJSet_iff.mp ha) (WeierstrassCurve.ofJ a) (WeierstrassCurve.ofJ_j a) P
      (by rwa [natCast_zsmul] at hP))
  rwa [WeierstrassCurve.ofJ_j] at h
