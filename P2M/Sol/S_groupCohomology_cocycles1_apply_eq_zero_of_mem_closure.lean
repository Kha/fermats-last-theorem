import Mathlib
import P2M.Util
namespace P2MW.S_groupCohomology_cocycles1_apply_eq_zero_of_mem_closure

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [CommRing k] [Group G] {M : Rep k G} (c : cocycles₁ M) {s : Set G}
    (hs : ∀ g ∈ s, c g = 0) {g : G} (hg : g ∈ Subgroup.closure s) : c g = 0 := by
  have hcoc := (mem_cocycles₁_iff (A := M) ⇑c).1 c.2
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact cocycles₁_map_one c
  | mul x y _ _ hx hy => rw [hcoc x y, hy, map_zero, zero_add, hx]
  | inv x _ hx =>
      have h := hcoc x⁻¹ x
      rw [inv_mul_cancel, cocycles₁_map_one, hx, map_zero, zero_add] at h
      exact h.symm
