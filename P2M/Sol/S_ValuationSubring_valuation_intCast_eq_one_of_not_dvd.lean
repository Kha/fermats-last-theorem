import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_ValuationSubring_valuation_natCast_eq_one_of_not_dvd
import P2M.Util
namespace P2MW.S_ValuationSubring_valuation_intCast_eq_one_of_not_dvd

set_option autoImplicit false

theorem solution {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {a : ℤ} (hqa : ¬ (q : ℤ) ∣ a) : A.valuation (a : K) = 1 := by
  have hn : ¬ q ∣ a.natAbs := fun h => hqa (Int.natCast_dvd.mpr h)
  have h1 := ValuationSubring.valuation_natCast_eq_one_of_not_dvd A hq hA hn
  rcases Int.natAbs_eq a with h | h
  · rw [h, Int.cast_natCast]; exact h1
  · rw [h, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact h1
