import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_isUnit_natCast_or_isUnit_natCast_of_coprime

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R] {m n : ℕ} (h : Nat.Coprime m n) :
    IsUnit (m : R) ∨ IsUnit (n : R) := by
  obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := R) h
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (huv ▸ isUnit_one) with hu | hv
  · exact Or.inl (isUnit_of_mul_isUnit_right hu)
  · exact Or.inr (isUnit_of_mul_isUnit_right hv)
