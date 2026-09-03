import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
namespace P2MW.S_ModularForm_coeffHeckeT_int

set_option autoImplicit false

open ModularForm

theorem solution (k : ℤ) (hk : 1 ≤ k) (p : ℕ) {a : ℕ → ℂ} (ha : ∀ n : ℕ, ∃ m : ℤ, a n = m) (n : ℕ) : ∃ m : ℤ, ModularForm.coeffHeckeT k p a n = m := by
  obtain ⟨m₁, hm₁⟩ := ha (n * p)
  rw [coeffHeckeT_apply, hm₁]
  split_ifs with h
  · obtain ⟨m₂, hm₂⟩ := ha (n / p)
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hk)
    refine ⟨m₁ + p ^ j * m₂, ?_⟩
    rw [hm₂, hj, zpow_natCast]
    push_cast
    ring
  · exact ⟨m₁, by simp⟩
