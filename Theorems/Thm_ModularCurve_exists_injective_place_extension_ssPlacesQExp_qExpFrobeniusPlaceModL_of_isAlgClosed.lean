import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed
    (p : ℕ) [Fact p.Prime]
    (κ K : Type*) [Field κ] [Field K] [IsAlgClosed κ] [IsAlgClosed K] [CharP κ p] [CharP K p] [Algebra κ K]
    (Γ : Subgroup SL(2, ℤ))
    [AlgebraicCurve.IsCurveOver κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)]
    [AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    (hfgκ : ∃ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ), Transcendental κ x ∧
      FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set ↥(ModularCurve.qExpFunctionFieldC κ Γ))) ↥(ModularCurve.qExpFunctionFieldC κ Γ))
    (hfgK : ∃ x : ↥(ModularCurve.qExpFunctionFieldC K Γ), Transcendental K x ∧
      FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set ↥(ModularCurve.qExpFunctionFieldC K Γ))) ↥(ModularCurve.qExpFunctionFieldC K Γ))
    (ι : ↥(ModularCurve.qExpFunctionFieldC κ Γ) →+* ↥(ModularCurve.qExpFunctionFieldC K Γ))
    (hι : ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ), ((ι x : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) (x : LaurentSeries κ)) :
    ∃ ext : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) → AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ),
      Function.Injective ext ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)),
        f ∈ v.toValuationSubring ↔ ι f ∈ (ext v).toValuationSubring) ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)),
        (∀ f : ↥(ModularCurve.qExpFunctionFieldC κ Γ), f ∈ v.toValuationSubring ↔ ι f ∈ w.toValuationSubring) → ext v = w) ∧
      (∀ w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ), w.toValuationSubring.comap ι ≠ ⊤ →
        ∃ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ), ext v = w) ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)), (ext v).ord (ι f) = v.ord f) ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (a : κ),
        v.HasValue f a ↔ (ext v).HasValue (ι f) (algebraMap κ K a)) ∧
      (∀ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ),
        v ∈ ModularCurve.ssPlacesQExp κ Γ p ↔ ext v ∈ ModularCurve.ssPlacesQExp K Γ p) ∧
      (∀ w ∈ ModularCurve.ssPlacesQExp K Γ p, ∃ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ), ext v = w) ∧
      (∀ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ),
        ext (ModularCurve.qExpFrobeniusPlaceModL κ Γ p v) = ModularCurve.qExpFrobeniusPlaceModL K Γ p (ext v)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed.solution
