import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂
attribute [-simp] Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

universe u v

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] (𝒪 : ValuationSubring K)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (ψ : 𝒪 →+* Ω)
    (W : WeierstrassCurve 𝒪) [W.IsElliptic] (n : ℕ) (hn : IsUnit ((n : ℕ) : (𝒪 : Type u)))
    (TK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Point) (TΩ : ((W.map ψ).baseChange Ω).toAffine.Point)
    (hT : (TK = 0 ∧ TΩ = 0) ∨ ∃ (xT yT : 𝒪)
      (hTK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K xT) (algebraMap 𝒪 K yT))
      (hTΩ : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ xT) (ψ yT)),
      TK = WeierstrassCurve.Affine.Point.some _ _ hTK ∧ TΩ = WeierstrassCurve.Affine.Point.some _ _ hTΩ)
    (hTKn : (n : ℤ) • TK = 0) (hTΩn : (n : ℤ) • TΩ = 0) :
    ∃ (p q : Polynomial 𝒪) (c : K) (c' : Ω), c ≠ 0 ∧ c' ≠ 0 ∧
      Polynomial.map (algebraMap 𝒪 K) p • (1 : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.CoordinateRing) +
          Polynomial.map (algebraMap 𝒪 K) q •
            WeierstrassCurve.Affine.CoordinateRing.mk ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine Y =
        algebraMap K _ c * weilNum (W.map (algebraMap 𝒪 K)) K n TK ∧
      Polynomial.map ψ p • (1 : ((W.map ψ).baseChange Ω).toAffine.CoordinateRing) +
          Polynomial.map ψ q • WeierstrassCurve.Affine.CoordinateRing.mk ((W.map ψ).baseChange Ω).toAffine Y =
        algebraMap Ω _ c' * weilNum (W.map ψ) Ω n TΩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring.solution
