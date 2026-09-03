import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairSplit
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_isGoodDivisor_add_of_ord_residue_eq_neg
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isGoodDivisor_add_of_ord_residue_eq_neg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k ↥(modularFunctionFieldC k 1)) (lam : k → k) (hsd : R.SplitDatum S₀ E D₁ D₂ lam)
    (G : ↥(modularFunctionFieldBar (1 * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
    (hG₁ : R.R₁.residue ⟨G, h₁⟩ ≠ 0) (hG₂ : R.R₂.residue ⟨G, h₂⟩ ≠ 0)
    (hGE : G ∈ riemannRochSpace E)
    (DG : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDG : ∀ W, DG W = W.ord G)
    (Δ₁ Δ₂ : Divisor k ↥(modularFunctionFieldC k 1))
    (hΔ₁ : ∀ v, Δ₁ v = v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k 1)))
    (hΔ₂ : ∀ v, Δ₂ v = v.ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k 1)))
    (hfix : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
      v ≠ P.redFst (cuspInftyBar (1 * q)) →
      v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k 1)) + D₁ v = 0 ∧
      (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k 1)) +
        D₂ (frobOnPlacesGeomLevel k 1 data hKr v) = 0)
    (hcusp₁ : (P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k 1)) +
      D₁ (P.redFst (cuspInftyBar (1 * q))) = 0)
    (hcusp₂ : (P.redSnd (cuspZeroBar (1 * q))).ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k 1)) +
      D₂ (P.redSnd (cuspZeroBar (1 * q))) = 0) :
    (∀ W, 0 ≤ (E + DG) W) ∧ P.IsGoodDivisor (E + DG) ∧
      Finsupp.mapDomain P.redFst (P.fstPart (E + DG)) = D₁ + Δ₁ ∧
      Finsupp.mapDomain P.redSnd (P.sndPart (E + DG)) = D₂ + Δ₂ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_isGoodDivisor_add_of_ord_residue_eq_neg.solution
