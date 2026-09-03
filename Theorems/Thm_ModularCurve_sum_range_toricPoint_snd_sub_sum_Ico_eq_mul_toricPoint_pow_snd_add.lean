import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add

set_option autoImplicit false

open ModularCurve

universe u

theorem ModularCurve.sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (hc0 : c ≠ 0) (hcℓ : c ^ ℓ ≠ 1) :
    ∑ j ∈ Finset.range ℓ, (toricPoint K 1 (c * ζ ^ j)).2 -
        ∑ j ∈ Finset.Ico 1 ℓ, (toricPoint K 1 (ζ ^ j)).2 =
      (ℓ : LaurentSeries K) ^ 3 * (toricPoint K ℓ (c ^ ℓ)).2 +
        HahnSeries.C ((ℓ : K) ^ 2 * ((ℓ : K) - 1) / 2) * (toricPoint K ℓ (c ^ ℓ)).1 -
          HahnSeries.C (((ℓ : K) ^ 2 - 1) / 24) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add.solution
