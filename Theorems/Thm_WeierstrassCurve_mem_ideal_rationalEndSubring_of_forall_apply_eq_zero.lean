import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX
attribute [-simp] WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero

set_option autoImplicit false
open scoped Quaternion

theorem WeierstrassCurve.mem_ideal_rationalEndSubring_of_forall_apply_eq_zero
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic]
    (a b : ℚ) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (L : Ideal ↥(WeierstrassCurve.rationalEndSubring κ X₀))
    (n : ℕ) (hn : (n : κ) ≠ 0) (hnL : (n : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) ∈ L)
    (r : ↥(WeierstrassCurve.rationalEndSubring κ X₀))
    (hr : ∀ P : (X₀.baseChange κ).toAffine.Point,
      (∀ l ∈ L, (l : AddMonoid.End (X₀.baseChange κ).toAffine.Point) P = 0) →
        (r : AddMonoid.End (X₀.baseChange κ).toAffine.Point) P = 0) :
    r ∈ L := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.solution
