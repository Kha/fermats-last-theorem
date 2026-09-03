import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_sum_range_toricPoint_fst_sub_sum_Ico_eq_mul_toricPoint_pow_fst_add_C

set_option autoImplicit false

open ModularCurve

universe u

theorem ModularCurve.sum_range_toricPoint_fst_sub_sum_Ico_eq_mul_toricPoint_pow_fst_add_C
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (hc0 : c ≠ 0) (hcℓ : c ^ ℓ ≠ 1) :
    ∑ j ∈ Finset.range ℓ, (toricPoint K 1 (c * ζ ^ j)).1 -
        ∑ j ∈ Finset.Ico 1 ℓ, (toricPoint K 1 (ζ ^ j)).1 =
      (ℓ : LaurentSeries K) ^ 2 * (toricPoint K ℓ (c ^ ℓ)).1 +
        HahnSeries.C (((ℓ : K) ^ 2 - 1) / 12) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_range_toricPoint_fst_sub_sum_Ico_eq_mul_toricPoint_pow_fst_add_C.solution
