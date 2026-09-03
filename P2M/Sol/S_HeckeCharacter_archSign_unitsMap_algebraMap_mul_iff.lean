import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_archRealProjTau_unitsMap_algebraMap
import P2M.Util
namespace P2MW.S_HeckeCharacter_archSign_unitsMap_algebraMap_mul_iff

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem solution
    (K : Type*) [Field K] [NumberField K] (τ : K →+* ℝ) (α : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ) :
    archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α * u) ↔
      (0 < τ α ↔ archSign K τ u) := by
  unfold archSign
  rw [archRealProjTau_mul, archRealProjTau_unitsMap_algebraMap]
  have hα : (τ α : ℝ) ≠ 0 := by
    rw [← archRealProjTau_unitsMap_algebraMap]; exact archRealProjTau_ne_zero K τ _
  have hu : archRealProjTau K τ u ≠ 0 := archRealProjTau_ne_zero K τ u
  rcases lt_or_gt_of_ne hα with hα' | hα' <;> rcases lt_or_gt_of_ne hu with hu' | hu'
  · exact ⟨fun _ => ⟨fun h => absurd h (lt_asymm hα'), fun h => absurd h (lt_asymm hu')⟩, fun _ => mul_pos_of_neg_of_neg hα' hu'⟩
  · refine ⟨fun h => ?_, fun h => absurd (h.mpr hu') (lt_asymm hα')⟩
    exact absurd h (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hα'.le hu'.le))
  · refine ⟨fun h => ?_, fun h => absurd (h.mp hα') (lt_asymm hu')⟩
    exact absurd h (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hα'.le hu'.le))
  · exact ⟨fun _ => ⟨fun _ => hu', fun _ => hα'⟩, fun _ => mul_pos hα' hu'⟩
