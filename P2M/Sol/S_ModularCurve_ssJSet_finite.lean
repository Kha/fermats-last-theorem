module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Definitions.Def_ModularCurve_SupersingularModuli
public import Theorems.Thm_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero
public import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_ssJSet_finite
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_ssJSet_finite.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "ssJSet mem_ssJSet_iff" end ModularCurve
p2m_open_scoped "ModularCurve" in
open Polynomial in

theorem ModularCurve.solution_aux_pow_q_sq {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] {a : K} (ha : a ∈ ModularCurve.ssJSet q K) : a ^ (q ^ 2) = a := by
  have h := WeierstrassCurve.j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero q (WeierstrassCurve.ofJ a)
    (fun P hP => (ModularCurve.mem_ssJSet_iff.mp ha) (WeierstrassCurve.ofJ a) (WeierstrassCurve.ofJ_j a) P
      (by rwa [natCast_zsmul] at hP))
  rwa [WeierstrassCurve.ofJ_j] at h

p2m_open_scoped "ModularCurve" in
open Polynomial in

theorem ModularCurve.solution_main {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] : (ModularCurve.ssJSet q K).Finite := by
  have hq : 1 < q ^ 2 :=
    calc 1 < q := (Fact.out : q.Prime).one_lt
      _ ≤ q * q := Nat.le_mul_self q
      _ = q ^ 2 := (sq q).symm
  have hne : (X ^ (q ^ 2) - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  refine ((X ^ (q ^ 2) - X : K[X]).roots.toFinset.finite_toSet).subset ?_
  intro a ha
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, IsRoot, eval_sub, eval_pow,
    eval_X, sub_eq_zero]
  exact ModularCurve.solution_aux_pow_q_sq q ha

theorem solution (q : ℕ) [Fact q.Prime]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    (ModularCurve.ssJSet q K).Finite := ModularCurve.solution_main q
