import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Theorems.Thm_ValuationSubring_valuation_intCast_eq_pow_padicValInt
import P2M.Util
namespace P2MW.S_ValuationSubring_valuation_ratCast_eq_zpow_padicValRat

set_option autoImplicit false

theorem solution {K : Type*} [Field K] [CharZero K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {r : ℚ} (hr : r ≠ 0) : A.valuation (r : K) = A.valuation (q : K) ^ padicValRat q r := by
  have hnum : r.num ≠ 0 := Rat.num_ne_zero.mpr hr
  have hden : (r.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr r.den_nz
  have hq0 : A.valuation (q : K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (by exact_mod_cast hq.ne_zero)
  have hcast : (r : K) = (r.num : K) / ((r.den : ℤ) : K) := by
    rw [Rat.cast_def]; push_cast; rfl
  rw [hcast, map_div₀, ValuationSubring.valuation_intCast_eq_pow_padicValInt A hq hA hnum,
    ValuationSubring.valuation_intCast_eq_pow_padicValInt A hq hA hden, padicValRat_def,
    padicValInt.of_nat, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
