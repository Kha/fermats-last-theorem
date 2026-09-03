import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range

set_option autoImplicit false

theorem RingHom.exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range
    {k K : Type*} [Field k] [Field K] (φ : k →+* K) {X : Type*} {n : ℕ}
    (f : Fin n → X → K) (hf : ∀ i x, f i x ∈ Set.range φ)
    (c : Fin n → K) (hc : ∀ x, ∑ i, c i * f i x = 0) :
    ∃ (m : ℕ) (d : Fin m → K) (v : Fin m → Fin n → k),
      (∀ j x, ∑ i, φ (v j i) * f i x = 0) ∧ ∀ i, c i = ∑ j, d j * φ (v j i) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range.solution
