import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Differentials
import P2M.Util
import P2M.Sol.S_ModularCurve_smul_D_jqModC_ne_zero
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

theorem ModularCurve.smul_D_jqModC_ne_zero {K : Type*} [Field K] {ℓ : ℕ} [NeZero ℓ]
    [PerfectField K] (x₀ : ModularCurve.modularFunctionFieldC K ℓ)
    [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set (ModularCurve.modularFunctionFieldC K ℓ)))
      (ModularCurve.modularFunctionFieldC K ℓ)]
    {z : ModularCurve.modularFunctionFieldC K ℓ} (hz : z ≠ 0) :
    z • KaehlerDifferential.D K (ModularCurve.modularFunctionFieldC K ℓ)
      ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K ℓ⟩ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_smul_D_jqModC_ne_zero.solution
