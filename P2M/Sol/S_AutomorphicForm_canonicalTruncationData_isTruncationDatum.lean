import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import P2M.Util
namespace P2MW.S_AutomorphicForm_canonicalTruncationData_isTruncationDatum
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
theorem solution
    (L : Type) [Field L] [NumberField L] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    0 < canonicalTruncationFloor L α β ∧ IsCompact (canonicalTruncationTranslates L α β) ∧
      canonicalTruncationDomain L α β ⊆ ⋃ y ∈ canonicalTruncationTranslates L α β,
        (· * y) '' WindowedSiegel.centreCutSiegelSet L (canonicalTruncationFloor L α β)
          (canonicalTruncationWindow L α β) (canonicalTruncationLowerCut L α β)
          (canonicalTruncationUpperCut L α β) ∧
      canonicalTruncationDomain L α β ⊆
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∧
      IsFundamentalDomain (globalPoints (𝓞 L) L).range (canonicalTruncationDomain L α β)
        ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
          {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := by
  obtain ⟨Tcov, c, hc, u, hcov⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet L
  obtain ⟨d₁', d₂', tset, Φ₀, -, -, hΦ₀s, hΦ₀, hΦ₀S⟩ :=
    AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
      L c u 1 2 Tcov hc one_pos one_lt_two (hcov 1 2 two_pos one_le_two) α β hα hαβ
  have hTc : IsCompact (↑tset : Set (AdelicGL2 (𝓞 L) L)) := tset.finite_toSet.isCompact
  exact AutomorphicForm.canonicalTruncationData_spec L ⟨((c, u, d₁', d₂'), ↑tset, Φ₀), hc, hTc, hΦ₀S, hΦ₀s, hΦ₀⟩

#print axioms solution
