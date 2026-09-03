import Definitions.Def_ModularCurve_ChartSemicontinuity
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_mem_chartLocalSetFst_of_split
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.mem_chartLocalSetFst_of_split
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    {v : Place k (modularFunctionFieldC k N)} {S : Set (modularFunctionFieldBar (N * q))}
    (hqN : ¬ q ∣ N) (hint : ∀ s ∈ S, s ∈ R.R₁.integers)
    (hregv : ∀ (s : modularFunctionFieldBar (N * q)) (hs : s ∈ S),
      (R.residue₁ ⟨s, hint s hs⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring)
    (hregOver : ∀ s ∈ S, ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = v → s ∈ W.toValuationSubring)
    (hnIncl : ∀ φ : modularFunctionFieldBar N,
      heckeAlphaBar (AlgebraicClosure ℚ) N q φ ∈ R.R₁.integers →
      (∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u₀ = v → φ ∈ u₀.toValuationSubring) →
      ∃ (s : modularFunctionFieldBar (N * q)) (_ : s ∈ S) (e : modularFunctionFieldBar (N * q)) (he : e ∈ S),
        ¬ v.HasValue (R.residue₁ ⟨e, hint e he⟩) (0 : k) ∧ heckeAlphaBar (AlgebraicClosure ℚ) N q φ * e = s)
    (hE : ChartEtaleAt R v S)
    {good bad : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → Prop}
    (hsplit : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = v → good W ∨ bad W)
    (hsep : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      bad W → P.reduceFst W = v →
        ∃ (u : modularFunctionFieldBar (N * q)) (hu : u ∈ S),
          ¬ v.HasValue (R.residue₁ ⟨u, hint u hu⟩) (0 : k) ∧ 0 < W.ord u)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers)
    (hreg : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      good W → P.reduceFst W = v → 0 ≤ W.ord f) :
    f ∈ chartLocalSetFst R v S := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_mem_chartLocalSetFst_of_split.solution
