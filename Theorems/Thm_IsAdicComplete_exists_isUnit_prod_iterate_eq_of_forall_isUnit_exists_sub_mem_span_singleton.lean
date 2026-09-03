import Mathlib
import P2M.Util
import P2M.Sol.S_IsAdicComplete_exists_isUnit_prod_iterate_eq_of_forall_isUnit_exists_sub_mem_span_singleton

set_option autoImplicit false

theorem IsAdicComplete.exists_isUnit_prod_iterate_eq_of_forall_isUnit_exists_sub_mem_span_singleton
    {D : Type*} [CommRing D] (ϖ : D) (hϖ : ϖ ∈ nonZeroDivisors D)
    [IsAdicComplete (Ideal.span {ϖ}) D]
    (τ : D →+* D) (n : ℕ) (hτn : ∀ x, τ^[n] x = x) (hτϖ : τ ϖ = ϖ)
    (hT : ∃ x₀ : D, (∑ i ∈ Finset.range n, τ^[i] x₀) - 1 ∈ Ideal.span {ϖ})
    (hN : ∀ c : D, IsUnit c → τ c = c →
      ∃ u : D, IsUnit u ∧ (∏ i ∈ Finset.range n, τ^[i] u) - c ∈ Ideal.span {ϖ})
    (c : D) (hc : IsUnit c) (hτc : τ c = c) :
    ∃ u : D, IsUnit u ∧ (∏ i ∈ Finset.range n, τ^[i] u) = c := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_exists_isUnit_prod_iterate_eq_of_forall_isUnit_exists_sub_mem_span_singleton.solution
