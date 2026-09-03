import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DegeneracyTower
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ
set_option autoImplicit false

open AlgebraicCurve
open ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq
    {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    [IsCurveOver k ↥(modularFunctionFieldC k N)] {red : ↥A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (hι : (towerInclBar (AlgebraicClosure ℚ)
      (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q)).toRingHom.IsIntegral)
    (a : k) (hss : a ∈ ssJSet q k)
    (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hVj : ∃ x : A, red x = a ∧
      0 < V'.ord (jFun 1 q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
        (x : AlgebraicClosure ℚ)))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : V.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
      (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q)) hι = V') :
    P.reduceFst V ∈ ssPlaces q N k ∧ (P.reduceFst V).evalAt (jGeomGen k N) = a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq.solution
