import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import P2M.Util
import P2M.Sol.S_ModularCurve_XZeroP_exists_completeDVR_algebraMap_ringHom_adicCompletion_stalk_twoChartIntegralModel_gamma0_mul
attribute [-instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec
attribute [-simp] compl₂EDS_two

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XZeroP.exists_completeDVR_algebraMap_ringHom_adicCompletion_stalk_twoChartIntegralModel_gamma0_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)

    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (z₂ : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂))
    (ϖz₂ : (AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)
    (hϖz₂ : ϖz₂ = (((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.germ ⊤ z₂ trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))))
    (hz₂ : ϖz₂ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂))
    (y₂ : ↥(XFin A (↥K₂) j₂)) (hy₂ : (ιFin A (↥K₂) j₂).base y₂ = z₂)
    (hss₂ : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K₂) j₂) →+* Ω),
      RingHom.ker φ = y₂.asIdeal → φ (jChartFin A (↥K₂) j₂) ∈ ModularCurve.ssJSet p Ω)

    (𝔶₂ : Ideal ↥(chartAlgFin A (↥K₂) j₂)) (h𝔶₂ : 𝔶₂ = y₂.asIdeal) :
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsDiscreteValuationRing W₂)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W₂) W₂) (τ₂ : A →+* W₂)
      (_ : IsLocalRing.maximalIdeal W₂ = Ideal.span {τ₂ ϖ})
      (σ₂ : W₂ →+* (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂))),
      (∀ a : A, σ₂ (τ₂ a) =
        algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.germ ⊤ z₂ trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) ∧
      ∀ f : ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂), ∃ o : W₂,
        algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) f - σ₂ o ∈
          Ideal.map (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)))
            (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XZeroP_exists_completeDVR_algebraMap_ringHom_adicCompletion_stalk_twoChartIntegralModel_gamma0_mul.solution
