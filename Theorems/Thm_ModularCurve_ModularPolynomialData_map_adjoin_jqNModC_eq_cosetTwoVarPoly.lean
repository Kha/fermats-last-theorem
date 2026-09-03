import Mathlib
import Definitions.Def_ModularCurve_ModularEquationQ
import Definitions.Def_ModularCurve_PrimCosetReps
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_map_adjoin_jqNModC_eq_cosetTwoVarPoly
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
attribute [-simp] ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.ModularPolynomialData.map_adjoin_jqNModC_eq_cosetTwoVarPoly
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (data : ModularCurve.ModularPolynomialData M)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ M) :
    (data.toJqNField K).map (algebraMap (ModularCurve.jqNField K M) (LaurentSeries K)) =
        ModularCurve.cosetTwoVarPoly ζ M (ModularCurve.jqModC K) ∧
    ((data.toJqNField K).map (algebraMap (ModularCurve.jqNField K M) (LaurentSeries K))).Splits ∧
    (data.toJqNField K).Separable ∧
    (data.toJqNField K).rootSet (LaurentSeries K) =
      ModularCurve.cosetConj ζ (ModularCurve.jqModC K) '' ↑(ModularCurve.primCosetReps M) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_map_adjoin_jqNModC_eq_cosetTwoVarPoly.solution
