import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat

open scoped NumberField Classical

theorem NumberField.mixedEmbedding.exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat
    {s : 𝓞 ℚ} (hs : s ≠ 0) (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (a b : NumberField.mixedEmbedding.mixedSpace ℚ),
        0 < NumberField.mixedEmbedding.norm a → 0 < NumberField.mixedEmbedding.norm b →
        ∀ (τ : ℚ → NumberField.mixedEmbedding.mixedSpace ℚ), τ 0 = 0 →
        ∀ (T : Finset (ℚ × ℚ)),
          (∀ p ∈ T, p ≠ 0 ∧ (∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * p.1) ∧
            (∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * p.2)) →
          ∑ p ∈ T, ((1 + ‖a * NumberField.mixedEmbedding ℚ p.1‖) ^ M)⁻¹ *
              ((1 + ‖τ p.1 + b * NumberField.mixedEmbedding ℚ p.2‖) ^ M)⁻¹
            ≤ C * (1 + (NumberField.mixedEmbedding.norm a)⁻¹)
                * (1 + (NumberField.mixedEmbedding.norm b)⁻¹)
                * (min 1 ((NumberField.mixedEmbedding.norm a)⁻¹ ^ N)
                    + min 1 ((NumberField.mixedEmbedding.norm b)⁻¹ ^ N)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat.solution
