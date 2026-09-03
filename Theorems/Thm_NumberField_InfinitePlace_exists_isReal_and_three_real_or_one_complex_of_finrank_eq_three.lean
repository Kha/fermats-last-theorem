import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlace_exists_isReal_and_three_real_or_one_complex_of_finrank_eq_three

set_option autoImplicit false

open NumberField

theorem NumberField.InfinitePlace.exists_isReal_and_three_real_or_one_complex_of_finrank_eq_three
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3) :
    ∃ (w₀ : InfinitePlace K) (h₀ : w₀.IsReal),
      (∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), ∀ w : InfinitePlace K, w = wC ∨ w = w₀) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_exists_isReal_and_three_real_or_one_complex_of_finrank_eq_three.solution
