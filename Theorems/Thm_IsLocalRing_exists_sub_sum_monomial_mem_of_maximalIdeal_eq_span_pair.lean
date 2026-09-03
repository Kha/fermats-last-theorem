import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair
    {W R : Type*} [CommRing W] [CommRing R] [IsLocalRing R] [Algebra W R]
    (y₀ y₁ : R) (hmax : maximalIdeal R = Ideal.span {y₀, y₁})
    (hres : ∀ r : R, ∃ w : W, r - algebraMap W R w ∈ maximalIdeal R)
    (J : Ideal R) (D : ℕ) (h₀ : y₀ ^ D ∈ J) (h₁ : y₁ ^ D ∈ J) (r : R) :
    ∃ c : ℕ × ℕ → W,
      r - ∑ p ∈ Finset.range D ×ˢ Finset.range D, algebraMap W R (c p) * (y₀ ^ p.1 * y₁ ^ p.2) ∈ J := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair.solution
