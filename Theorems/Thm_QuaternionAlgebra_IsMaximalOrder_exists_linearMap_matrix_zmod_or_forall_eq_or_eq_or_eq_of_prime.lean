import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (ℓ : ℕ) [Fact ℓ.Prime] :
    (∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))) ∨
    ((∀ J : Submodule ℤ ℍ[ℚ, a, b], (∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J) →
        Submodule.span ℤ ((ℓ : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ≤ J → J ≤ Λ →
          J = Submodule.span ℤ ((ℓ : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ∨
            (J : Set ℍ[ℚ, a, b]) = {x | x ∈ Λ ∧ ∃ n : ℤ, nrd x = (ℓ : ℚ) * n} ∨ J = Λ) ∧
      (∃ x ∈ Λ, (∃ n : ℤ, nrd x = (ℓ : ℚ) * n) ∧ ¬ (∃ n : ℤ, nrd x = (ℓ : ℚ) ^ 2 * n))) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime.solution
