import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve
theorem ModularCurve.PlaceSpecialization.finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun
    {q : ℕ} [Fact q.Prime] (c : AlgebraicClosure ℚ) (hc : c ≠ 0) :
    FiniteDimensional
        ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({PlaceSpecialization.jFun (q := q)
              + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c
                * PlaceSpecialization.jqFun (q := q)} : Set ↥(modularFunctionFieldBar (1 * q))))
        ↥(modularFunctionFieldBar (1 * q))
      ∧ Module.finrank
          ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({PlaceSpecialization.jFun (q := q)
                + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c
                  * PlaceSpecialization.jqFun (q := q)} : Set ↥(modularFunctionFieldBar (1 * q))))
          ↥(modularFunctionFieldBar (1 * q)) = 2 * q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun.solution
