import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "QuaternionAlgebra~trd~IsMaximalOrder"

universe v

theorem QuaternionAlgebra.IsOrder.casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    {R : Type v} [Ring R] (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    (∀ c : R ⊗[ℤ] R, (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)) →
        ∃ n : ℤ, LinearMap.mul' ℤ R c = (n : R)) ∧
    ∃ c : R ⊗[ℤ] R, (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)) ∧
      LinearMap.mul' ℤ R c ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero.solution
