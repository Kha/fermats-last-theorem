import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import P2M.Util
namespace P2MW.S_NumberField_Idele_exists_forall_measure_eq_mul_idelicHaar

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal

theorem solution (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure] :
    ∃ d : ℝ≥0∞, d ≠ 0 ∧ d ≠ ⊤ ∧ ∀ s : Set (AdeleRing (𝓞 K) K)ˣ, ν s = d * NumberField.Idele.idelicHaar K s := by
  obtain rfl : (‹MeasurableSpace (AdeleRing (𝓞 K) K)ˣ› : MeasurableSpace (AdeleRing (𝓞 K) K)ˣ) =
      NumberField.Idele.ideleBorel K := BorelSpace.measurable_eq
  letI : MeasurableSpace (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.ideleBorel K
  haveI : BorelSpace (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.borelSpace_ideleBorel K
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  haveI : SigmaCompactSpace (AdeleRing (𝓞 K) K)ˣ := by
    haveI : SigmaCompactSpace (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
      (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 K) K)).symm.isClosedEmbedding.sigmaCompactSpace
    exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace
  set μ := NumberField.Idele.idelicHaar K with hμ
  set d : ℝ≥0∞ := (Measure.haarScalarFactor ν μ : ℝ≥0∞) with hd
  have hd0 : d ≠ 0 := by
    rw [hd, Ne, ENNReal.coe_eq_zero]
    exact (Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ).ne'

  have hmeasurable : ∀ s : Set (AdeleRing (𝓞 K) K)ˣ, MeasurableSet s → ν s = d * μ s := by
    intro s hs
    have hmono : Monotone fun n : ℕ => s ∩ compactCovering (AdeleRing (𝓞 K) K)ˣ n :=
      fun m n hmn => Set.inter_subset_inter_right _ (compactCovering_subset _ hmn)
    have hunion : ⋃ n, s ∩ compactCovering (AdeleRing (𝓞 K) K)ˣ n = s := by
      rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
    have hn : ∀ n, ν (s ∩ compactCovering _ n) = d * μ (s ∩ compactCovering _ n) := by
      intro n
      have hc : IsCompact (closure (s ∩ compactCovering (AdeleRing (𝓞 K) K)ˣ n)) :=
        (isCompact_compactCovering _ n).closure_of_subset Set.inter_subset_right
      rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν μ hc, hd, ENNReal.smul_def, smul_eq_mul]
    rw [← hunion, Monotone.measure_iUnion hmono, Monotone.measure_iUnion hmono, ENNReal.mul_iSup]
    exact iSup_congr hn
  have hext : ν = d • μ := Measure.ext fun s hs => by rw [hmeasurable s hs, Measure.smul_apply, smul_eq_mul]
  refine ⟨d, hd0, by rw [hd]; exact ENNReal.coe_ne_top, fun s => ?_⟩
  rw [hext, Measure.smul_apply, smul_eq_mul]
