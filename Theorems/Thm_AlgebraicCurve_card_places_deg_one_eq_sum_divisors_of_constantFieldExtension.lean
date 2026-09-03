import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring

set_option autoImplicit false

theorem AlgebraicCurve.card_places_deg_one_eq_sum_divisors_of_constantFieldExtension
    {k k' F F' : Type*} [Field k] [Finite k] [Field k'] [Finite k'] [Field F] [Field F']
    [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
    [Algebra k F] [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    [AlgebraicCurve.IsCurveOver k' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range) :
    Nat.card {w : AlgebraicCurve.Place k' F' | w.deg = 1} =
      ∑ d ∈ Nat.divisors (Module.finrank k k'),
        d * Nat.card {v : AlgebraicCurve.Place k F | v.deg = d} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.solution
