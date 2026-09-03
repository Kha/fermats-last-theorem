import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

set_option autoImplicit false

open AlgebraicCurve ModularCurve.CharPModel in
theorem ModularCurve.exists_sub_mem_nonunits_of_integral_affineBaseInf
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M]
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)))
    (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
    (hb : ∃ p : Polynomial (affineBaseInf M A), p.Monic ∧
      Polynomial.eval₂ (affineBaseInf M A).subtype b p = 0)
    (a₀ : A)
    (hj : 0 < w.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full M (jq_mem M))⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))⁻¹
      - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
        (a₀ : AlgebraicClosure ℚ))) :
    ∃ a : A, (b - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
      (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.solution
