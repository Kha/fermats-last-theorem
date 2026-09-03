import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Theorems.Thm_ValuationSubring_valuation_intCast_eq_pow_padicValInt
import P2M.Util
namespace P2MW.S_ValuationSubring_valuation_intCast_eq_pow_pow_of_dvd

set_option autoImplicit false

theorem solution {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {z : ℤ} (hz : z ≠ 0) {ℓ : ℕ} (hℓ : ℓ ∣ padicValInt q z) :
    A.valuation (z : K) = (A.valuation (q : K) ^ (padicValInt q z / ℓ)) ^ ℓ := by
  rw [ValuationSubring.valuation_intCast_eq_pow_padicValInt A hq hA hz, ← pow_mul,
    Nat.div_mul_cancel hℓ]
