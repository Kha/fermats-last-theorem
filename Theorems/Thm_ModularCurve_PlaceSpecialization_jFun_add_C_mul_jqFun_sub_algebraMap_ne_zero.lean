import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve
theorem ModularCurve.PlaceSpecialization.jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero
    {q : ℕ} [Fact q.Prime] (c a : AlgebraicClosure ℚ) :
    PlaceSpecialization.jFun (q := q)
        + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c * PlaceSpecialization.jqFun (q := q)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) a ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero.solution
