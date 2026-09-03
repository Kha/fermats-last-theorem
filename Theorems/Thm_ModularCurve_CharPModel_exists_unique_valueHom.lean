import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_exists_unique_valueHom
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open AlgebraicCurve
theorem ModularCurve.CharPModel.exists_unique_valueHom {K F : Type*} [Field K] [Field F] [Algebra K
    F]
    [IsAlgClosed K] (A : ValuationSubring K) (g : F) (B₀ : Subring F)
    (hint : ∀ b : B₀,
      ∃ p : Polynomial (Subring.closure (algebraMap K F '' (A : Set K) ∪ {g})),
        p.Monic ∧
          Polynomial.eval₂ (Subring.closure (algebraMap K F '' (A : Set K) ∪ {g})).subtype
            (b : F) p = 0)
    (w : Place K F)
    (hw : ∃ a : A, g - algebraMap K F (a : K) ∈ w.toValuationSubring.nonunits) :
    ∃! φ : B₀ →+* A, ∀ b : B₀,
      (b : F) - algebraMap K F ((φ b : A) : K) ∈ w.toValuationSubring.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_exists_unique_valueHom.solution
