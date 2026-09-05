module

public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Mathlib.FieldTheory.RatFunc.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable

@[expose] public section
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
open AlgebraicCurve
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
theorem AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable
    {K : Type*} [Field K] (E : Type*) [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E] [Algebra.IsSeparable (RatFunc K) E] :
    HasPrincipalDivisors K E := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.solution
