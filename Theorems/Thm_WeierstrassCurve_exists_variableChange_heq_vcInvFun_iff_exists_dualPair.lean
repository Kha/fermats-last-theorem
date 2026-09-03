import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_heq_vcInvFun_iff_exists_dualPair
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂
attribute [-simp] Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

theorem WeierstrassCurve.exists_variableChange_heq_vcInvFun_iff_exists_dualPair
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (E A E' : WeierstrassCurve κ) [E.IsElliptic] [A.IsElliptic] [E'.IsElliptic]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ0 : (ℓ : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ)
    (φ : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point)
    (hφ : φ ∈ WeierstrassCurve.rationalHomSet κ E A) (hker : φ.ker = AddSubgroup.zmultiples Q)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
      (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet κ E V → α Q = 0 →
          ∃ β ∈ WeierstrassCurve.rationalHomSet κ A V, α = β.comp φ)
    (C : Set E.toAffine.Point) (C' : Set E'.toAffine.Point) :
    (∃ γ : WeierstrassCurve.VariableChange κ, γ • A = E' ∧
        ∀ T ∈ C, ∃ T' ∈ C', HEq (WeierstrassCurve.Affine.Point.vcInvFun γ A.toAffine (φ T)) T') ↔
      ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E E', ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E' E,
        ψ.ker = AddSubgroup.zmultiples Q ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧
          ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ C, ψ T ∈ C' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_heq_vcInvFun_iff_exists_dualPair.solution
