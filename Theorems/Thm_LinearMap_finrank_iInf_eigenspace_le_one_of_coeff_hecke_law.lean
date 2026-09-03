import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law

set_option autoImplicit false

theorem LinearMap.finrank_iInf_eigenspace_le_one_of_coeff_hecke_law
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : ℕ → V →ₗ[K] K)
    (hinj : ∀ v : V, (∀ n : ℕ, 1 ≤ n → a n v = 0) → v = 0)
    (T : ℕ → V →ₗ[K] V) (c : ℕ → K)
    (hlaw : ∀ ℓ : ℕ, ℓ.Prime → ∀ n : ℕ, 1 ≤ n → ∀ v : V,
      a n (T ℓ v) = a (n * ℓ) v + (if ℓ ∣ n then c ℓ * a (n / ℓ) v else 0))
    (μ : ℕ → K) :
    (∀ v ∈ ⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ), a 1 v = 0 → v = 0) ∧
    Module.finrank K ↥(⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ)) ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law.solution
