import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff

set_option autoImplicit false

open NumberField

theorem NumberField.exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
    (K : Type*) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥)
    (N : Set (K →+* ℝ)) :
    ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔪 ∧
      ∀ φ : K →+* ℝ, φ (algebraMap (𝓞 K) K α) < 0 ↔ φ ∈ N := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff.solution
