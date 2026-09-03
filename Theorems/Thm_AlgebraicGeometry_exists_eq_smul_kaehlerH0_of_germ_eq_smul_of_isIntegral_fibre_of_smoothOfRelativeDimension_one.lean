import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_eq_smul_kaehlerH0_of_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_eq_smul_kaehlerH0_of_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
    {R : Type u} [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    {κ : Type u} [Field κ] (q : R →+* κ) (hker : RingHom.ker q = Ideal.span {ϖ})
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    [Module.Flat R Ω[(𝒱.cover c).A0⁄R]] [Module.Flat R Ω[(𝒱.cover c).A1⁄R]] [Module.Flat R Ω[(𝒱.cover c).A01⁄R]]
    [IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom q)))]
    (x : X) (hx : x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base)
    (ω : ↥((𝒱.kaehlerSections c).H0))

    (hc0 : ∀ h0 : x ∈ 𝒱.U0, ((X.presheaf.germ 𝒱.U0 x h0).hom : (𝒱.cover c).A0 →+* X.presheaf.stalk x).comp
        (algebraMap R (𝒱.cover c).A0) =
      ((X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).comp
        (RingHom.id R))
    (hc1 : ∀ h1 : x ∈ 𝒱.U1, ((X.presheaf.germ 𝒱.U1 x h1).hom : (𝒱.cover c).A1 →+* X.presheaf.stalk x).comp
        (algebraMap R (𝒱.cover c).A1) =
      ((X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).comp
        (RingHom.id R))
    (hgerm : letI : Algebra R (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
      ∃ η : Ω[X.presheaf.stalk x⁄R],
        (∃ h0 : x ∈ 𝒱.U0, KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A0) (B := X.presheaf.stalk x)
            (RingHom.id R) (X.presheaf.germ 𝒱.U0 x h0).hom (hc0 h0) ω.val.1 = ϖ • η) ∨
        (∃ h1 : x ∈ 𝒱.U1, KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A1) (B := X.presheaf.stalk x)
            (RingHom.id R) (X.presheaf.germ 𝒱.U1 x h1).hom (hc1 h1) ω.val.2 = ϖ • η)) :
    ∃ ω' : ↥((𝒱.kaehlerSections c).H0), ω = ϖ • ω' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_eq_smul_kaehlerH0_of_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one.solution
