import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
attribute [-simp] ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
set_option autoImplicit false

theorem ModularCurve.exists_monic_natDegree_le_aeval_jqModC_eq_zero (K : Type*) [Field K] (p : ℕ) [NeZero p]
    (data : ModularCurve.ModularPolynomialData p) (hsym : ModularCurve.EvalSymm data.Φ)
    (hpsi : ModularCurve.dedekindPsi p = p + 1) :
    ∃ P : Polynomial (IntermediateField.adjoin K ({ModularCurve.jqNModC K p} :
        Set (LaurentSeries K))),
      P.Monic ∧ P.natDegree ≤ p + 1 ∧ Polynomial.aeval (ModularCurve.jqModC K) P = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero.solution
