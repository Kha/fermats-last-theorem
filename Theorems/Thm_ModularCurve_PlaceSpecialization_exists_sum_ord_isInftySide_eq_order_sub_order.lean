import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ

open AlgebraicCurve IsLocalRing ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.PlaceSpecialization.exists_sum_ord_isInftySide_eq_order_sub_order
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (x : ↥(modularFunctionFieldBar (1 * q))) (hx0 : x ≠ 0)
    (hx : x ∈ Algebra.adjoin (AlgebraicClosure ℚ)
      ({(PlaceSpecialization.jFun (q := q))⁻¹, PlaceSpecialization.tInfty (q := q)} :
        Set ↥(modularFunctionFieldBar (1 * q)))) :
    ∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A)
      (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))),
      c ≠ 0 ∧ coeffMap A.subtype y = c • (x : LaurentSeries (AlgebraicClosure ℚ)) ∧
      coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      (∀ W, W ∈ S ↔ P.IsInftySide W ∧ W ≠ cuspInftyBar (1 * q) ∧ W.ord x ≠ 0) ∧
      ∑ W ∈ S, W.ord x = (coeffMap (IsLocalRing.residue A) y).order - y.order := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.solution
