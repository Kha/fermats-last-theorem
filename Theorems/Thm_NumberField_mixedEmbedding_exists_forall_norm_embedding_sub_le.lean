import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le

theorem NumberField.mixedEmbedding.exists_forall_norm_embedding_sub_le (K : Type*) [Field K]
    [NumberField K] : ∃ U : ℝ, ∀ ξ : NumberField.InfinitePlace K → ℂ,
      (∀ w : NumberField.InfinitePlace K, w.IsReal → (ξ w).im = 0) →
        ∃ b : NumberField.RingOfIntegers K, ∀ w : NumberField.InfinitePlace K,
          ‖w.embedding (b : K) - ξ w‖ ≤ U := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le.solution
