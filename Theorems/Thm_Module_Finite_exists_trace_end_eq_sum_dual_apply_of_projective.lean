import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Finite_exists_trace_end_eq_sum_dual_apply_of_projective

set_option autoImplicit false

universe u v

open scoped BigOperators

theorem Module.Finite.exists_trace_end_eq_sum_dual_apply_of_projective
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] :
    ∃ τ : (M →ₗ[A] M) →ₗ[A] A,
      ∀ (n : ℕ) (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)),
        (∀ m : M, ∑ i, φ i m • x i = m) →
          ∀ f : M →ₗ[A] M, τ f = ∑ i, φ i (f (x i)) := by p2m_exact_reverting @_root_.P2MW.S_Module_Finite_exists_trace_end_eq_sum_dual_apply_of_projective.solution
