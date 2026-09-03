import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (σ : A ≃+* A) (hσ : ∀ a : A, σ a - a ∈ IsLocalRing.maximalIdeal A)
    (n : ℕ) (hn : 1 ≤ n) (c : A) (hc : c ≠ 0)
    (π : A) (hπ : π ^ n = c)
    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ n = c * u)
    (αt : A) (hα : σ π = αt * π) :
    ∃ m : A, m ∈ IsLocalRing.maximalIdeal A ∧ σ ϖt = αt * ϖt * (1 + m) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul.solution
