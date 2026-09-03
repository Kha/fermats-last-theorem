import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
    {R : Type u} [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    {κ : Type u} [Field κ] (q : R →+* κ) (hker : RingHom.ker q = Ideal.span {ϖ})
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    [IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom q)))]
    (ω : ↥((𝒱.kaehlerSections c).H0)) :
    (∀ x : X, x ∈ 𝒱.U0 → x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base →
        (∃ ω₀ : Ω[(𝒱.cover c).A0⁄R], ω.val.1 = ϖ • ω₀) → ∃ ω₁ : Ω[(𝒱.cover c).A1⁄R], ω.val.2 = ϖ • ω₁) ∧
    (∀ x : X, x ∈ 𝒱.U1 → x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base →
        (∃ ω₁ : Ω[(𝒱.cover c).A1⁄R], ω.val.2 = ϖ • ω₁) → ∃ ω₀ : Ω[(𝒱.cover c).A0⁄R], ω.val.1 = ϖ • ω₀) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one.solution
