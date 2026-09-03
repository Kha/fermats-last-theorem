import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_finite_and_sum_finrank_eq_of_exact_of_exact_of_exact

set_option autoImplicit false

universe u

theorem LinearMap.finite_and_sum_finrank_eq_of_exact_of_exact_of_exact
    {k : Type u} [Field k] (A B Q : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module k (A n)] [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
    [∀ n, AddCommGroup (Q n)] [∀ n, Module k (Q n)]
    (f : ∀ n, A n →ₗ[k] B n) (g : ∀ n, B n →ₗ[k] Q n) (δ : ∀ n, Q n →ₗ[k] A (n + 1))
    (hfg : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    (hgδ : ∀ n, LinearMap.range (g n) = LinearMap.ker (δ n))
    (hδf : ∀ n, LinearMap.range (δ n) = LinearMap.ker (f (n + 1)))
    (hA : ∀ n, Module.Finite k (A n)) (hQ : ∀ n, Module.Finite k (Q n))
    (M : ℕ) (hf0 : Function.Injective (f 0)) (hfM : Function.Injective (f M)) :
    (∀ n, Module.Finite k (B n)) ∧
      ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (B n) : ℤ) =
        ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (A n) : ℤ) +
          ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (Q n) : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_finite_and_sum_finrank_eq_of_exact_of_exact_of_exact.solution
