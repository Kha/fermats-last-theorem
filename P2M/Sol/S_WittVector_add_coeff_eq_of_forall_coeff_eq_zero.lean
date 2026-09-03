import Mathlib
import P2M.Util
namespace P2MW.S_WittVector_add_coeff_eq_of_forall_coeff_eq_zero

set_option autoImplicit false

universe u

theorem solution
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] (x y : WittVector p S) (r : ℕ)
    (hx : ∀ i : ℕ, i < r → x.coeff i = 0) :
    ∀ i : ℕ, i < r → (x + y).coeff i = y.coeff i := by
  intro i hi
  have hker : WittVector.truncate r x = 0 := (WittVector.mem_ker_truncate r x).2 hx
  have h := congrArg (fun t : TruncatedWittVector p r S => t.coeff ⟨i, hi⟩) (map_add (WittVector.truncate r) x y)
  simp only [hker, zero_add, WittVector.coeff_truncate] at h
  exact h
