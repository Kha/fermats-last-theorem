import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le

theorem NumberField.InfinitePlace.exists_sum_prod_inv_one_add_mul_pow_le
    (F : Type) [Field F] [NumberField F] {s : NumberField.RingOfIntegers F} (hs : s ≠ 0) (N : ℕ) :
    ∃ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : NumberField.InfinitePlace F → ℝ, (∀ w, 0 < y w) →
      1 ≤ ∏ w, y w ^ w.mult →
      ∀ T : Finset F,
        (∀ ξ ∈ T, ξ ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers F, (a : F) = (s : F) * ξ) →
        ∑ ξ ∈ T, ∏ w : NumberField.InfinitePlace F, ((1 + y w * w ξ) ^ M)⁻¹
          ≤ C * ((∏ w : NumberField.InfinitePlace F, y w ^ w.mult) ^ N)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le.solution
