import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero
    {k F : Type*} [Field k] [Field F] [Algebra k F] (x : F) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F]
    (S : Finset (Place k F)) (P : Place k F) (hP : P ∈ S)
    (hS : ∀ Q ∈ S, x ∈ Q.toValuationSubring) :
    ∃ y : F, IsIntegral (Algebra.adjoin k ({x} : Set F)) y ∧ P.ord y = 1 ∧
      ∀ Q ∈ S, Q ≠ P → Q.ord y = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.solution
