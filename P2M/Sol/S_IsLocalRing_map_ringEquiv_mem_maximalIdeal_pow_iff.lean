import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_map_ringEquiv_mem_maximalIdeal_pow_iff

set_option autoImplicit false
set_option maxHeartbeats 4000000
open IsLocalRing

open scoped NNReal

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsLocalRing R]
    (σ : R ≃+* R) {k : ℕ} {x : R} : σ x ∈ maximalIdeal R ^ k ↔ x ∈ maximalIdeal R ^ k := by
  have hmap : ∀ (τ : R ≃+* R) {y : R}, y ∈ maximalIdeal R ^ k → τ y ∈ maximalIdeal R ^ k := by
    intro τ y hy
    have hle : Ideal.map (τ : R →+* R) (maximalIdeal R) ≤ maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      rw [mem_maximalIdeal, mem_nonunits_iff] at hz
      intro hu; exact hz (by simpa using hu.map (τ.symm : R →+* R))
    have h1 : τ y ∈ Ideal.map (τ : R →+* R) (maximalIdeal R ^ k) := Ideal.mem_map_of_mem _ hy
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hle k h1
  refine ⟨fun h => ?_, hmap σ⟩
  have h2 := hmap σ.symm h
  rwa [RingEquiv.symm_apply_apply] at h2
