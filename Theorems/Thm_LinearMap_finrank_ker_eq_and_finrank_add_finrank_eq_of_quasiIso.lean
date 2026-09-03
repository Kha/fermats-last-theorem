import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso

set_option autoImplicit false

universe u v

theorem LinearMap.finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso
    {A : Type u} [Field A]
    (K : ℕ → Type v) [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)] [∀ i, Module.Finite A (K i)]
    (δ : ∀ i, K i →ₗ[A] K (i + 1))
    (C : ℕ → Type v) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)] (d : ∀ i, C i →ₗ[A] C (i + 1))
    (φ : ∀ i, K i →ₗ[A] C i) (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
    (h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
    (h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
    (hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i))
    (hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i)) :
    Module.finrank A ↥(LinearMap.ker (d 0)) = Module.finrank A ↥(LinearMap.ker (δ 0)) ∧
      ∀ (i : ℕ) (H : Type v) [AddCommGroup H] [Module A H] (ψ : ↥(LinearMap.ker (d (i + 1))) →ₗ[A] H),
        Function.Surjective ψ →
        LinearMap.ker ψ = (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype →
        Module.finrank A H +
            Module.finrank A ↥((LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) =
          Module.finrank A ↥(LinearMap.ker (δ (i + 1))) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso.solution
