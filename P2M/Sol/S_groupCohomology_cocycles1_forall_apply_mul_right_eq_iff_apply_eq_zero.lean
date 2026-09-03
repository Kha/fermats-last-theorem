import Mathlib
import P2M.Util
namespace P2MW.S_groupCohomology_cocycles1_forall_apply_mul_right_eq_iff_apply_eq_zero

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [CommRing k] [Group G] {M : Rep k G} (c : cocycles₁ M) (u : G) :
    (∀ g : G, c (g * u) = c g) ↔ c u = 0 := by
  have hcoc := (mem_cocycles₁_iff (A := M) ⇑c).1 c.2
  constructor
  · intro h
    have h1 := h 1
    rw [one_mul, cocycles₁_map_one] at h1
    exact h1
  · intro hu g
    rw [hcoc g u, hu, map_zero, zero_add]
