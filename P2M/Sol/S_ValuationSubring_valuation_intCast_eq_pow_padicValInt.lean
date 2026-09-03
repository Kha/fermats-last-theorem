import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Theorems.Thm_ValuationSubring_valuation_intCast_eq_one_of_not_dvd
import P2M.Util
namespace P2MW.S_ValuationSubring_valuation_intCast_eq_pow_padicValInt

set_option autoImplicit false

theorem solution {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {z : ℤ} (hz : z ≠ 0) : A.valuation (z : K) = A.valuation (q : K) ^ padicValInt q z := by
  haveI : Fact q.Prime := ⟨hq⟩

  set v : ℕ := padicValNat q z.natAbs with hv
  have hn0 : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hdvd : q ^ v ∣ z.natAbs := pow_padicValNat_dvd
  obtain ⟨c, hc⟩ := hdvd
  have hqc : ¬ (q : ℤ) ∣ (c : ℤ) := by
    intro h
    have h' : q ∣ c := Int.natCast_dvd_natCast.mp h
    obtain ⟨d, rfl⟩ := h'
    have : q ^ (v + 1) ∣ z.natAbs := ⟨d, by rw [hc]; ring⟩
    exact pow_succ_padicValNat_not_dvd hn0 this
  have hcval : A.valuation ((c : ℤ) : K) = 1 :=
    ValuationSubring.valuation_intCast_eq_one_of_not_dvd A hq hA hqc
  have habs : A.valuation (z : K) = A.valuation ((z.natAbs : ℤ) : K) := by
    rcases Int.natAbs_eq z with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, Valuation.map_neg]
  have hpv : padicValInt q z = v := rfl
  rw [habs, hpv, Int.cast_natCast, hc, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow,
    show ((c : ℕ) : K) = ((c : ℤ) : K) by norm_cast, hcval, mul_one]
