import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_mul_heq
import P2M.Util
namespace P2MW.S_WeierstrassCurve_equivOfVariableChangeEq_symm_conj_vcInvFun

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace CONJE100

variable {K : Type*} [Field K] [DecidableEq K]

def castPt {V V' : WeierstrassCurve.Affine K} (h : V = V') (P : V.Point) : V'.Point := h ▸ P

omit [DecidableEq K] in
theorem heq_iff_castPt_eq {V V' : WeierstrassCurve.Affine K} (h : V = V') (P : V.Point) (Q : V'.Point) :
    HEq P Q ↔ castPt h P = Q := by
  subst h; simp [castPt]

theorem equivOfVariableChangeEq_symm_apply {V W : WeierstrassCurve.Affine K} (C : VariableChange K)
    (h : C • W = V) (T : W.Point) :
    (Point.equivOfVariableChangeEq h).symm T = castPt h (Point.vcInvFun C W T) := by
  subst h; rfl

theorem vcInvFun_congr_heq {C₁ C₂ : VariableChange K} (h : C₁ = C₂) (W : WeierstrassCurve.Affine K) (T : W.Point) :
    HEq (Point.vcInvFun C₁ W T) (Point.vcInvFun C₂ W T) := by
  subst h; rfl

theorem vcInvFun_castPt_heq (C : VariableChange K) {V V' : WeierstrassCurve.Affine K} (h : V = V') (Q : V.Point) :
    HEq (Point.vcInvFun C V Q) (Point.vcInvFun C V' (castPt h Q)) := by
  subst h; rfl

theorem main (E : WeierstrassCurve K) (C γ : VariableChange K) (hγ : γ • E = E) :
    ∃ hγ' : (C * γ * C⁻¹) • (C • E) = C • E,
      ∀ T : E.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := (C • E).toAffine) hγ').symm (Point.vcInvFun C E.toAffine T) =
          Point.vcInvFun C E.toAffine ((Point.equivOfVariableChangeEq (W := E.toAffine) hγ).symm T) := by
  have hγ' : (C * γ * C⁻¹) • (C • E) = C • E := by
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, hγ]
  refine ⟨hγ', fun T => ?_⟩
  rw [equivOfVariableChangeEq_symm_apply, equivOfVariableChangeEq_symm_apply]
  rw [← heq_iff_castPt_eq]

  have h1 : HEq (Point.vcInvFun (C * γ * C⁻¹) (C • E).toAffine (Point.vcInvFun C E.toAffine T))
      (Point.vcInvFun (C * γ * C⁻¹ * C) E.toAffine T) :=
    (Point.vcInvFun_mul_heq (C * γ * C⁻¹) C E.toAffine T).symm
  have h2 : HEq (Point.vcInvFun (C * γ * C⁻¹ * C) E.toAffine T) (Point.vcInvFun (C * γ) E.toAffine T) :=
    vcInvFun_congr_heq (by group) E.toAffine T
  have h3 : HEq (Point.vcInvFun (C * γ) E.toAffine T)
      (Point.vcInvFun C (γ • E).toAffine (Point.vcInvFun γ E.toAffine T)) :=
    Point.vcInvFun_mul_heq C γ E.toAffine T
  have h4 : HEq (Point.vcInvFun C (γ • E).toAffine (Point.vcInvFun γ E.toAffine T))
      (Point.vcInvFun C E.toAffine (castPt (congrArg WeierstrassCurve.toAffine hγ) (Point.vcInvFun γ E.toAffine T))) :=
    vcInvFun_castPt_heq C (congrArg WeierstrassCurve.toAffine hγ) _
  exact ((h1.trans h2).trans h3).trans h4

end CONJE100

theorem solution
    {K : Type*} [Field K] [DecidableEq K]
    (E : WeierstrassCurve K) (C γ : WeierstrassCurve.VariableChange K) (hγ : γ • E = E) :
    ∃ hγ' : (C * γ * C⁻¹) • (C • E) = C • E,
      ∀ T : E.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := (C • E).toAffine) hγ').symm (Point.vcInvFun C E.toAffine T) =
          Point.vcInvFun C E.toAffine ((Point.equivOfVariableChangeEq (W := E.toAffine) hγ).symm T) :=
  CONJE100.main E C γ hγ
