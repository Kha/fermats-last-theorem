import Mathlib
import Definitions.Def_FreyPackage_RouteAReversePinSeam
import Definitions.Def_FreyPackage_EigenformResidualAttachment
import P2M.Util
import P2M.Sol.S_FreyPackage_canonicalModelCongruence_of_eigenformResidualAttachment_of_congruence_outside
attribute [-instance] FreyCurve.instIsEllipticRatFreyCurve FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two
attribute [-simp] WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero

theorem FreyPackage.canonicalModelCongruence_of_eigenformResidualAttachment_of_congruence_outside (P : FreyPackage)
    (hatt : ∀ M : ℕ, 0 < M → P.EigenformResidualAttachmentAt M)
    {M : ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f.IsNormalizedEigenform)
    {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf P.freyCurve)
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (P.p : integralClosure ℤ ℂ) ∈ 𝔪)
    (S₀ : Finset ℕ)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) :
    ∀ ℓ₀ : ℕ, ℓ₀.Prime → (FreyPackage.freyCurveInt P).IsGoodPrimeFor ℓ₀ → ¬ ℓ₀ ∣ M → ℓ₀ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ₀ ∧
        a - (((FreyPackage.freyCurveInt P).apOfModel ℓ₀ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_canonicalModelCongruence_of_eigenformResidualAttachment_of_congruence_outside.solution
