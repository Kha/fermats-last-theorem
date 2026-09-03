import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finite_sections_not_le_preimage_of_smoothOfRelativeDimension_one
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.finite_sections_not_le_preimage_of_smoothOfRelativeDimension_one
    {L : Type u} [Field L] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of L))
    [IsIntegral X] [SmoothOfRelativeDimension 1 c] [QuasiCompact c]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Set.Finite {q : Spec (CommRingCat.of L) ⟶ X |
      q ≫ c = 𝟙 (Spec (CommRingCat.of L)) ∧ ¬ ((⊤ : (Spec (CommRingCat.of L)).Opens) ≤ q ⁻¹ᵁ U)} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finite_sections_not_le_preimage_of_smoothOfRelativeDimension_one.solution
