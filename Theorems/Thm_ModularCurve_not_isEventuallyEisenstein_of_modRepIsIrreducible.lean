import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_ModularCurve_MazurPrincipleCore
import P2M.Util
import P2M.Sol.S_ModularCurve_not_isEventuallyEisenstein_of_modRepIsIrreducible
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four
attribute [-simp] WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply
set_option autoImplicit false

theorem ModularCurve.not_isEventuallyEisenstein_of_modRepIsIrreducible (p : ℕ) [Fact p.Prime]
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (i : ℕ) (hi : (p - 1) ∣ 2 * i)
    (𝔪 : Ideal HeckeAlg) (h𝔪 : 𝔪 ≠ ⊤) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (hcong : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → W.IsGoodPrimeFor ℓ →
      heckeGen ⟨ℓ, hℓ⟩ - ((ℓ ^ i * W.apOfModel ℓ : ℤ) : HeckeAlg) ∈ 𝔪) :
    ¬ IsEventuallyEisenstein 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_not_isEventuallyEisenstein_of_modRepIsIrreducible.solution
