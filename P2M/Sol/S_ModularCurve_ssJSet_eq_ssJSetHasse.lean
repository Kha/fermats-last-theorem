module

public import Mathlib
public import Definitions.Def_ModularCurve_SupersingularModuli
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Theorems.Thm_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
public import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_ssJSet_eq_ssJSetHasse
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

open ModularCurve

theorem solution (q : ℕ) [Fact q.Prime] (hq : q ≠ 2)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ssJSet q K = ssJSetHasse q K := by
  ext j
  simp only [ModularCurve.ssJSet, ModularCurve.ssJSetHasse, Set.mem_setOf_eq]
  constructor
  · intro h W _ hj
    exact (W.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero q hq).mp (h W hj)
  · intro h W _ hj
    exact (W.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero q hq).mpr (h W hj)
