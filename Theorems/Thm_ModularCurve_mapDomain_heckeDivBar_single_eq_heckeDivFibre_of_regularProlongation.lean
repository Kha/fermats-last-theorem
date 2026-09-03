import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero
attribute [-simp] ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation
    (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (q : ℕ) [hq' : Fact q.Prime] [NeZero (N * q)]
    (hαq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβq : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hαc : HeckeAlphaCIntegral (ResidueField ↥A) N q)
    (hβc : HeckeBetaCIntegral (ResidueField ↥A) N q)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    [HasPrincipalDivisors (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q)]
    (hdeg1 : ∀ Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q),
      Y.deg = 1)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    (r₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      → Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ P, D P = P.ord (f : modularFunctionFieldBar N)) →
      ∀ Q, Finsupp.mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (R : RegularProlongation A (modularFunctionFieldBar (N * q))
      (charLDegeneracyRoof (ResidueField ↥A) N q))
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      → Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q))
    (hr : ∀ f : R.integers, R.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ P, D P = P.ord (f : modularFunctionFieldBar (N * q))) →
      ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f))
    (hRα : ∀ f : R₁.integers,
      ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.integers,
        R.residue ⟨_, h⟩ = heckeAlphaC (ResidueField ↥A) N q (R₁.residue f))
    (hRβ : ∀ f : R₁.integers,
      ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.integers,
        R.residue ⟨_, h⟩ = heckeBetaC (ResidueField ↥A) N q (R₁.residue f))
    (hdegα : ∀ v, Divisor.degree
        (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq (Finsupp.single v 1))
      = Divisor.degree
        (Divisor.pullbackAlong (heckeAlphaC (ResidueField ↥A) N q) hαc (Finsupp.single (r₁ v) 1)))
    (hdegβ : ∀ v, Divisor.degree
        (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))
      = Divisor.degree
        (Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N q) hβc (Finsupp.single (r₁ v) 1))) :
    ∀ v, Finsupp.mapDomain r₁ (heckeDivBar hαq hβq (Finsupp.single v 1))
      = heckeDivFibre (ResidueField ↥A) N q hβc hαc (Finsupp.single (r₁ v) 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation.solution
