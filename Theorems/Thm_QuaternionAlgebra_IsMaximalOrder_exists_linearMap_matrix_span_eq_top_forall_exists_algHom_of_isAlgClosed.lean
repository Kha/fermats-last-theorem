import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_span_eq_top_forall_exists_algHom_of_isAlgClosed
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra hiding nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne

universe u v

theorem QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_span_eq_top_forall_exists_algHom_of_isAlgClosed
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k : Type u) [Field k] [IsAlgClosed k] (hqq' : IsUnit ((q * q' : ℕ) : k)) :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) k,

      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧

      Submodule.span k (Set.range φ) = ⊤ ∧

      ∀ (R : Type v) [Ring R] [Algebra k R] (ρ : ↥Λ →ₗ[ℤ] R),
        (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = 1) →
        (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
            ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ x * ρ y) →
        ∃ ψ : Matrix (Fin 2) (Fin 2) k →ₐ[k] R, ∀ x : ↥Λ, ψ (φ x) = ρ x := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_span_eq_top_forall_exists_algHom_of_isAlgClosed.solution
