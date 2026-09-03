import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff

set_option autoImplicit false

open scoped TensorProduct

universe v

theorem RingHom.exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff
    {R : Type v} [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (ℓ : ℕ) [Fact ℓ.Prime] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ψ : R →+* Matrix n n (ZMod ℓ)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : R, ψ x = 0 ↔ ∃ y : R, x = (ℓ : R) * y)
    (c₀ : R ⊗[ℤ] R) (hc₀ : ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c₀ = c₀ * ((1 : R) ⊗ₜ[ℤ] x)) (h₀ : c₀ ≠ 0) :
    ∃ c : R ⊗[ℤ] R, (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)) ∧
      ψ (LinearMap.mul' ℤ R c) = 1 := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff.solution
