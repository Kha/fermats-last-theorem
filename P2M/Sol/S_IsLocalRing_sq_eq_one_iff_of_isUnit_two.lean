import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_sq_eq_one_iff_of_isUnit_two

set_option autoImplicit false

namespace IsLocalRing p2m_export "IsLocalRing" "isUnit_or_isUnit_of_isUnit_add" end IsLocalRing
p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.mul_self_eq_one_iff_of_isUnit_two {R : Type} [CommRing R] [IsLocalRing R]
    (h2 : IsUnit (2 : R)) (u : R) : u * u = 1 ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro hu
    have hfac : (u - 1) * (u + 1) = 0 := by
      have : (u - 1) * (u + 1) = u * u - 1 := by ring
      rw [this, hu, sub_self]
    have h2' : IsUnit ((u + 1) + (1 - u)) := by
      have : (u + 1) + (1 - u) = (2 : R) := by ring
      rwa [this]
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h2' with h | h
    · left
      have := (h.mul_left_eq_zero).mp hfac
      exact sub_eq_zero.mp this
    · right
      have hfac' : (u + 1) * (1 - u) = 0 := by
        have : (u + 1) * (1 - u) = -((u - 1) * (u + 1)) := by ring
        rw [this, hfac, neg_zero]
      have := (h.mul_left_eq_zero).mp hfac'
      exact eq_neg_of_add_eq_zero_left this
  · rintro (rfl | rfl) <;> ring

theorem solution {R : Type} [CommRing R] [IsLocalRing R]
    (h2 : IsUnit (2 : R)) (u : R) : u ^ 2 = 1 ↔ u = 1 ∨ u = -1 := by
  rw [sq, IsLocalRing.mul_self_eq_one_iff_of_isUnit_two h2]
