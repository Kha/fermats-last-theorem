import Mathlib
import P2M.Util
namespace P2MW.S_ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat

theorem ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat
    (D : Type*) {C : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D] (hD : ¬ IsField D)
    [CommRing C] [Algebra D C] [Module.Finite D C] [Module.Flat D C]
    (m : Ideal C) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 := by
  have hle : m.height ≤ (1 : ℕ) := by
    rw [Ideal.height_le_iff]
    intro q hq hqm
    have hlt : q.comap (algebraMap D C) < m.comap (algebraMap D C) :=
      Ideal.IsIntegral.comap_lt_comap hqm
    have hqbot : q.comap (algebraMap D C) = ⊥ := by
      by_contra hne
      have hmax : (q.comap (algebraMap D C)).IsMaximal :=
        Ring.DimensionLEOne.maximalOfPrime hne inferInstance
      exact hlt.ne (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hlt.le)
    have h0 : q.height = 0 := by
      rw [Ideal.height_eq_zero_iff]
      refine ⟨⟨hq, bot_le⟩, fun q' hq' hle' => ?_⟩
      by_contra hnot
      haveI := hq'.1
      have hlt' : q' < q := lt_of_le_of_ne hle' (fun e => hnot (e ▸ le_rfl))
      have := Ideal.IsIntegral.comap_lt_comap (R := D) hlt'
      rw [hqbot] at this
      exact not_lt_bot this
    simp [h0]
  have hge : (1 : ℕ∞) ≤ m.height := by
    have hmu : (m.under D).IsMaximal := Ideal.IsMaximal.under D m
    have hne : m.under D ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hmu hD
    haveI : Algebra.HasGoingDown D C := Algebra.HasGoingDown.of_flat
    obtain ⟨P, hPm, hP, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := (⊥ : Ideal D))
      (q := m.under D) m (bot_lt_iff_ne_bot.mpr hne)
    by_contra hlt1
    have h0 : m.height = 0 := ENat.lt_one_iff_eq_zero.mp (not_le.mp hlt1)
    rw [Ideal.height_eq_zero_iff] at h0
    exact hPm.ne (le_antisymm hPm.le (h0.2 ⟨hP, bot_le⟩ hPm.le))
  have h1 : m.height = 1 := le_antisymm (by exact_mod_cast hle) hge
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), h1]
  rfl

theorem solution
    (D : Type*) {C : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D] (hD : ¬ IsField D)
    [CommRing C] [Algebra D C] [Module.Finite D C] [Module.Flat D C]
    (m : Ideal C) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 :=
  ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat D hD m
