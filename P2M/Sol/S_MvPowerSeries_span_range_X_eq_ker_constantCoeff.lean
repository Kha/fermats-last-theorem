import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Order
import Theorems.Thm_MvPowerSeries_mem_span_C_sup_ofList_take_iff
import P2M.Util
namespace P2MW.S_MvPowerSeries_span_range_X_eq_ker_constantCoeff

open MvPowerSeries

theorem solution {R : Type*} [CommRing R] (n : ℕ) :
    Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) R)) =
      RingHom.ker (constantCoeff : MvPowerSeries (Fin n) R →+* R) := by
  have mem_ofList_iff : ∀ F : MvPowerSeries (Fin n) R,
      F ∈ Ideal.ofList (List.ofFn fun i : Fin n => (X i : MvPowerSeries (Fin n) R)) ↔
        constantCoeff F = 0 := by
    intro F
    have hbot : Ideal.span {(0 : MvPowerSeries (Fin n) R)} = ⊥ :=
      Ideal.span_singleton_eq_bot.mpr rfl
    have hcollapse : Ideal.span {(C (0 : R) : MvPowerSeries (Fin n) R)} ⊔
        Ideal.ofList ((List.ofFn fun i : Fin n => (X i : MvPowerSeries (Fin n) R)).take n) =
        Ideal.ofList (List.ofFn fun i : Fin n => (X i : MvPowerSeries (Fin n) R)) := by
      rw [map_zero, hbot, bot_sup_eq, List.take_of_length_le]
      simp
    rw [← hcollapse, MvPowerSeries.mem_span_C_sup_ofList_take_iff]
    constructor
    · intro h
      have h0 := h 0 fun j _ => rfl
      rwa [zero_dvd_iff, coeff_zero_eq_constantCoeff_apply] at h0
    · intro hF m hm
      have hm0 : m = 0 := by
        ext j
        simpa using hm j j.isLt
      rw [hm0, zero_dvd_iff, coeff_zero_eq_constantCoeff_apply]
      exact hF
  have hcur : Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) R)) =
      Ideal.ofList (List.ofFn fun i : Fin n => (X i : MvPowerSeries (Fin n) R)) := by
    refine congrArg Ideal.span (Set.ext fun F => ?_)
    constructor
    · rintro ⟨i, rfl⟩
      exact (List.mem_ofFn' _ _).mpr ⟨i, rfl⟩
    · intro hF
      obtain ⟨i, hi⟩ := (List.mem_ofFn' _ _).mp hF
      exact ⟨i, hi⟩
  rw [hcur]
  ext F
  rw [RingHom.mem_ker, mem_ofList_iff]
