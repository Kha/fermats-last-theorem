import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le

open scoped NumberField Classical

theorem NumberField.mixedEmbedding.exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le
    (K : Type) [Field K] [NumberField K] {s : 𝓞 K} (hs : s ≠ 0) (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (a b : NumberField.mixedEmbedding.mixedSpace K),
        0 < NumberField.mixedEmbedding.norm a → 0 < NumberField.mixedEmbedding.norm b →
        ∀ (τ : K → NumberField.mixedEmbedding.mixedSpace K), τ 0 = 0 →
        ∀ (T : Finset (K × K)),
          (∀ p ∈ T, p ≠ 0 ∧ (∃ c : 𝓞 K, (c : K) = (s : K) * p.1) ∧
            (∃ c : 𝓞 K, (c : K) = (s : K) * p.2)) →
          ∑ p ∈ T, ((1 + ‖a * NumberField.mixedEmbedding K p.1‖) ^ M)⁻¹ *
              ((1 + ‖τ p.1 + b * NumberField.mixedEmbedding K p.2‖) ^ M)⁻¹
            ≤ C * (1 + (NumberField.mixedEmbedding.norm a)⁻¹ ^ 2)
                * (1 + (NumberField.mixedEmbedding.norm b)⁻¹ ^ 2)
                * (min 1 ((NumberField.mixedEmbedding.norm a)⁻¹ ^ N)
                    + min 1 ((NumberField.mixedEmbedding.norm b)⁻¹ ^ N)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le.solution
