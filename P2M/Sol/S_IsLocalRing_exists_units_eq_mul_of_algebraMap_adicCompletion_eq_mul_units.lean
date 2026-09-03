import Mathlib
import Theorems.Thm_IsLocalRing_comap_map_adicCompletion_eq
import P2M.Util
namespace P2MW.S_IsLocalRing_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_units

set_option autoImplicit false

open IsLocalRing

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal B) B)]
    (r s : B) (hs : s ≠ 0) (w : (AdicCompletion (IsLocalRing.maximalIdeal B) B)ˣ)
    (h : algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) r =
      algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) s * (w : AdicCompletion (IsLocalRing.maximalIdeal B) B)) :
    ∃ t : Bˣ, r = s * (t : B) := by
  set f := algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) with hf

  have hr : r ∈ Ideal.span ({s} : Set B) := by
    rw [← IsLocalRing.comap_map_adicCompletion_eq (Ideal.span ({s} : Set B)), Ideal.mem_comap, Ideal.map_span,
      Set.image_singleton]
    exact Ideal.mem_span_singleton'.mpr ⟨w, by rw [mul_comm]; exact h.symm⟩
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hr

  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have h0 := IsLocalRing.comap_map_adicCompletion_eq (⊥ : Ideal B)
    rw [Ideal.map_bot] at h0
    have hb' : b ∈ Ideal.comap f ⊥ := by rw [Ideal.mem_comap, Ideal.mem_bot]; exact hb
    rw [h0, Ideal.mem_bot] at hb'
    exact hb'

  have hft : f t = w := by
    have h2 : f s * f t = f s * w := by rw [← map_mul, mul_comm, ht, h]
    exact mul_left_cancel₀ ((map_ne_zero_iff f hinj).mpr hs) h2

  have htu : IsUnit t := by
    by_contra hnu
    have htm : t ∈ IsLocalRing.maximalIdeal B := hnu
    have h1 : (1 : B) ∈ Ideal.comap f ((IsLocalRing.maximalIdeal B).map f) := by
      rw [Ideal.mem_comap, map_one]
      have hw : f t * ↑w⁻¹ = 1 := by rw [hft, Units.mul_inv]
      rw [← hw]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem f htm)
    rw [IsLocalRing.comap_map_adicCompletion_eq] at h1
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal B).ne_top h1
  exact ⟨htu.unit, by rw [IsUnit.unit_spec, mul_comm, ht]⟩
