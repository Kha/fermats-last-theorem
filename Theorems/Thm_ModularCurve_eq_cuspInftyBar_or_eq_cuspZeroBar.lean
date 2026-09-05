module

public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar

@[expose] public section
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
attribute [-simp] ModularCurve.jqNModC_one

open ModularCurve AlgebraicCurve

theorem ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar (ℓ : ℕ) [Fact ℓ.Prime] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ)) (hc : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full ℓ)⟩ : modularFunctionFieldBar ℓ) w) : w = cuspInftyBar ℓ ∨ w = cuspZeroBar ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar.solution
