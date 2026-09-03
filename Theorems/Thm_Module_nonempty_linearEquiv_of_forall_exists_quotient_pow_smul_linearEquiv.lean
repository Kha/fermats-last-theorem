import Mathlib
import P2M.Util
import P2M.Sol.S_Module_nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv

set_option autoImplicit false

theorem Module.nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv
    {A : Type*} [CommRing A] [IsNoetherianRing A] (ϖ : A) (hϖ : ϖ ∈ Ideal.jacobson (⊥ : Ideal A))
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hM : ∀ m : M, ϖ • m = 0 → m = 0) (hN : ∀ n : N, ϖ • n = 0 → n = 0)
    (h : ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧
      Nonempty ((M ⧸ LinearMap.range (ϖ ^ k • (LinearMap.id : M →ₗ[A] M))) ≃ₗ[A]
        (N ⧸ LinearMap.range (ϖ ^ k • (LinearMap.id : N →ₗ[A] N))))) :
    Nonempty (M ≃ₗ[A] N) := by p2m_exact_reverting @_root_.P2MW.S_Module_nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv.solution
