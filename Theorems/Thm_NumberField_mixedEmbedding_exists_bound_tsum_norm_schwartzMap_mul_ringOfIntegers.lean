import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers

open scoped NumberField Classical

theorem NumberField.mixedEmbedding.exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers
    (K : Type*) [Field K] [NumberField K]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (Φ : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) V)
        (a : NumberField.mixedEmbedding.mixedSpace K),
        1 ≤ NumberField.mixedEmbedding.norm a →
          Summable (fun ξ : 𝓞 K => ‖Φ (a * NumberField.mixedEmbedding K (ξ : K))‖) ∧
          ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, ‖Φ (a * NumberField.mixedEmbedding K ((ξ : 𝓞 K) : K))‖ ≤
            C * SchwartzMap.seminorm ℝ M 0 Φ * (NumberField.mixedEmbedding.norm a)⁻¹ ^ N := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers.solution
