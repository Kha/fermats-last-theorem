import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_surjective_linearMap_ext_of_exact_of_free

set_option autoImplicit false

universe u

open CategoryTheory

theorem Module.exists_surjective_linearMap_ext_of_exact_of_free
    (R : Type u) [CommRing R] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Free R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (hex0 : ∀ z : K 0, δ 0 z = 0 → z = 0)
    (hex : ∀ i, i < n → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i))
    (M : Type u) [AddCommGroup M] [Module R M] :
    (∃ π : (K 0 →ₗ[R] M) →ₗ[R]
        Abelian.Ext (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) (n + 1),
      Function.Surjective π ∧ LinearMap.ker π = LinearMap.range (LinearMap.lcomp R M (δ 0))) ∧
    ∀ i : ℕ, i < n →
      ∃ π : LinearMap.ker (LinearMap.lcomp R M (δ i) : (K (i + 1) →ₗ[R] M) →ₗ[R] (K i →ₗ[R] M)) →ₗ[R]
          Abelian.Ext (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) (n - i),
        Function.Surjective π ∧
          ∀ φ, π φ = 0 ↔ ∃ ψ : K (i + 2) →ₗ[R] M, (φ : K (i + 1) →ₗ[R] M) = ψ ∘ₗ δ (i + 1) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_surjective_linearMap_ext_of_exact_of_free.solution
