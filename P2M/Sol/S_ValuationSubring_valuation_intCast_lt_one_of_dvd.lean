import Mathlib.RingTheory.Valuation.ValuationSubring
import P2M.Util
namespace P2MW.S_ValuationSubring_valuation_intCast_lt_one_of_dvd

set_option autoImplicit false

theorem solution {K : Type*} [Field K] (A : ValuationSubring K) {q : ℕ}
    (hA : A.valuation (q : K) < 1) {a : ℤ} (hqa : (q : ℤ) ∣ a) : A.valuation (a : K) < 1 := by
  obtain ⟨b, rfl⟩ := hqa
  rw [Int.cast_mul, Int.cast_natCast, map_mul]
  calc A.valuation (q : K) * A.valuation (b : K)
      ≤ A.valuation (q : K) * 1 :=
        mul_le_mul' le_rfl ((A.valuation_le_one_iff _).mpr (intCast_mem A b))
    _ = A.valuation (q : K) := mul_one _
    _ < 1 := hA
