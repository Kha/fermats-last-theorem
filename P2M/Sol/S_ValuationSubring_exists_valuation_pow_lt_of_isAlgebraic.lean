import Mathlib
import Theorems.Thm_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic
import P2M.Util
namespace P2MW.S_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] (O : ValuationSubring F)
    {π₀ : F} (h0 : O.valuation π₀ ≠ 0) (h1 : O.valuation π₀ < 1) (γ : O.ValueGroup) (hγ : γ ≠ 0) :
    ∃ n : ℕ, O.valuation π₀ ^ n < γ := by
  obtain ⟨y, rfl⟩ := O.valuation_surjective γ
  have hy : y ≠ 0 := fun h => hγ (by rw [h, Valuation.map_zero])
  rcases le_or_gt 1 (O.valuation y) with hle | hlt
  · exact ⟨1, by rw [pow_one]; exact h1.trans_le hle⟩
  obtain ⟨m, hm, k, hk⟩ := O.exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic h0 h1 hy

  have hym : O.valuation y ^ m ≤ O.valuation y := by
    calc O.valuation y ^ m = O.valuation y ^ (m - 1) * O.valuation y := by rw [← pow_succ, Nat.sub_add_cancel hm]
      _ ≤ 1 * O.valuation y := mul_le_mul_left (pow_le_one' hlt.le _) _
      _ = O.valuation y := one_mul _
  have hkpos : 0 < k := by
    by_contra hle
    push Not at hle
    have : 1 ≤ O.valuation π₀ ^ k := one_le_zpow_of_nonpos₀ (zero_lt_iff.mpr h0) h1.le hle
    rw [← hk] at this
    exact (lt_irrefl _) (this.trans_lt (pow_lt_one₀ zero_le' hlt (by omega)))
  obtain ⟨Kn, hKn⟩ := Int.eq_ofNat_of_zero_le hkpos.le
  refine ⟨Kn + 1, ?_⟩
  calc O.valuation π₀ ^ (Kn + 1) = O.valuation π₀ ^ Kn * O.valuation π₀ := pow_succ _ _
    _ < O.valuation π₀ ^ Kn * 1 := mul_lt_mul_of_pos_left h1 (pow_pos (zero_lt_iff.mpr h0) _)
    _ = O.valuation y ^ m := by rw [mul_one, hk, hKn, zpow_natCast]
    _ ≤ O.valuation y := hym
