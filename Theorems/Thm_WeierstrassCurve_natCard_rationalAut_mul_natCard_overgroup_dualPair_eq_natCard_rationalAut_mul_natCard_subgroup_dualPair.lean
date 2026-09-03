import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_rationalAut_mul_natCard_overgroup_dualPair_eq_natCard_rationalAut_mul_natCard_subgroup_dualPair
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂
attribute [-simp] Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

theorem WeierstrassCurve.natCard_rationalAut_mul_natCard_overgroup_dualPair_eq_natCard_rationalAut_mul_natCard_subgroup_dualPair
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic]
    (N : ℕ) [NeZero N] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    (C : AddSubgroup E.toAffine.Point) (C' : AddSubgroup E'.toAffine.Point)
    (hC : IsAddCyclic C ∧ Nat.card C = N) (hC' : IsAddCyclic C' ∧ Nat.card C' = N) :
    Nat.card {ι : E.toAffine.Point →+ E.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ E E ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ E E, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C.map ι = C} *
      Nat.card {Cp : AddSubgroup E'.toAffine.Point //
        (IsAddCyclic Cp ∧ Nat.card Cp = N * ℓ) ∧ Cp.map (ℓ • AddMonoidHom.id _) = C' ∧
        ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E' E, ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E E',
          ψ'.ker = Cp.map (N • AddMonoidHom.id _) ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ Cp, ψ' T ∈ C} =
    Nat.card {ι : E'.toAffine.Point →+ E'.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ E' E' ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ E' E', ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C'.map ι = C'} *
      Nat.card {D : AddSubgroup (E.baseChange κ).toAffine.Point //
        Nat.card D = ℓ ∧ ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E E', ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E' E,
          ψ.ker = D ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          (∀ T ∈ C, ψ T ∈ C') ∧ ∀ T ∈ C, ψ T = 0 → T = 0} := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_rationalAut_mul_natCard_overgroup_dualPair_eq_natCard_rationalAut_mul_natCard_subgroup_dualPair.solution
