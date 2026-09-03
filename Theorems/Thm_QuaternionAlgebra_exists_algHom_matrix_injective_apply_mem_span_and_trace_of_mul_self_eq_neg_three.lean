import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three
    (K : Type) [Field K] [CharZero K] [Algebra ℚ K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (O : Submodule ℤ K) (hO : O = Submodule.span ℤ ({1, ω} : Set K))
    {a b : ℚ} (ξ : ℍ[ℚ, a, b]) (hξ : ξ * ξ = algebraMap ℚ ℍ[ℚ, a, b] (-3))
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) :
    ∃ j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K, Function.Injective j ∧
      (∀ m ∈ Λ, ∀ i l : Fin 2, j m i l ∈ O) ∧
      ∀ (m : ℍ[ℚ, a, b]) (t : ℚ), m + star m = algebraMap ℚ ℍ[ℚ, a, b] t →
        j m 0 0 + j m 1 1 = algebraMap ℚ K t := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three.solution
