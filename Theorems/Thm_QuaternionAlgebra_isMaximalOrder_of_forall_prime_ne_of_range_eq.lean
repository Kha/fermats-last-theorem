import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_isMaximalOrder_of_forall_prime_ne_of_range_eq
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isMaximalOrder_of_forall_prime_ne_of_range_eq
    (p : ℕ) [Fact p.Prime] (O : Type*) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hsplit : ∀ ℓ : ℕ, [Fact ℓ.Prime] → ℓ ≠ p →
      Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]))
    (hmaxp : ∀ x : O, (∃ t n : ℤ, x * x - t • x + n • (1 : O) = 0 ∧ (p : ℤ) ∣ t ∧ (p : ℤ) ^ 2 ∣ n) →
      ∃ y : O, x = (p : ℤ) • y)
    {a b : ℚ} (θ : O →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    QuaternionAlgebra.IsMaximalOrder Λ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_isMaximalOrder_of_forall_prime_ne_of_range_eq.solution
