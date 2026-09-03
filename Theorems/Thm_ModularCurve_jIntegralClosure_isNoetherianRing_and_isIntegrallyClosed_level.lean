import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (dataNq : ModularPolynomialData (N * q))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsNoetherianRing ↥(jIntegralClosure (N * q) A K) ∧
    IsIntegrallyClosed ↥(jIntegralClosure (N * q) A K) ∧
    (∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ fieldOver (N * q) K →
        ∃ c s : LaurentSeries (AlgebraicClosure ℚ), c ∈ jIntegralClosure (N * q) A K ∧ s ∈ jRing A K ∧ s ≠ 0 ∧
          x * s = c) ∧
    (∃ s : Finset (LaurentSeries (AlgebraicClosure ℚ)),
      (↑s : Set (LaurentSeries (AlgebraicClosure ℚ))) ⊆ jIntegralClosure (N * q) A K ∧
      ∀ x ∈ jIntegralClosure (N * q) A K, ∃ f : LaurentSeries (AlgebraicClosure ℚ) → LaurentSeries (AlgebraicClosure ℚ),
        (∀ c ∈ s, f c ∈ jRing A K) ∧ x = ∑ c ∈ s, f c * c) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.solution
