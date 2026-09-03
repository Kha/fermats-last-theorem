import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero
attribute [-simp] ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve hiding nonempty_modularPolynomialData_of_squarefree modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi

theorem ModularCurve.finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] (hN : Squarefree N) (hN1 : 1 < N)
    (K : IntermediateField L (LaurentSeries L)) (x y : ↥K)
    (hx : (x : LaurentSeries L) = ModularCurve.jqModC L)
    (hy : (y : LaurentSeries L) = ModularCurve.jqNModC L N)
    [FiniteDimensional ↥(IntermediateField.adjoin L ({x} : Set ↥K)) ↥K] :
    Module.finrank ↥(IntermediateField.adjoin L ({y} : Set ↥K)) ↥K =
      Module.finrank ↥(IntermediateField.adjoin L ({x} : Set ↥K)) ↥K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree.solution
