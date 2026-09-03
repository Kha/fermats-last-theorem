import Mathlib
import P2M.Util
import P2M.Sol.S_Module_finrank_add_alternatingSum_finrank_eq_of_finite_complex

set_option autoImplicit false

universe u

theorem Module.finrank_add_alternatingSum_finrank_eq_of_finite_complex
    (k : Type u) [Field k]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module k (K i)] [∀ i, Module.Finite k (K i)]
    (δ : ∀ i, K i →ₗ[k] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (K i))
    (H0 : Type u) [AddCommGroup H0] [Module k H0] (e₀ : H0 ≃ₗ[k] LinearMap.ker (δ 0))
    (H : ℕ → Type u) [∀ i, AddCommGroup (H i)] [∀ i, Module k (H i)]
    (π : ∀ i, LinearMap.ker (δ (i + 1)) →ₗ[k] H i) (hπ : ∀ i, Function.Surjective (π i))
    (hπker : ∀ i, LinearMap.ker (π i) =
      (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) :
    (Module.finrank k H0 : ℤ) + ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * (Module.finrank k (H i) : ℤ) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.finrank k (K i) : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_Module_finrank_add_alternatingSum_finrank_eq_of_finite_complex.solution
