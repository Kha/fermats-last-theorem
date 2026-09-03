import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_not_forall_isUnit_tensorProduct_adicCompletion_of_forall_prime_ne

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.not_forall_isUnit_tensorProduct_adicCompletion_of_forall_prime_ne
    (p : ℕ) [Fact p.Prime] (O : Type*) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hsplit : ∀ ℓ : ℕ, [Fact ℓ.Prime] → ℓ ≠ p →
      Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]))
    {a b : ℚ} (e : ℚ ⊗[ℤ] O ≃ₐ[ℚ] ℍ[ℚ, a, b])
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_not_forall_isUnit_tensorProduct_adicCompletion_of_forall_prime_ne.solution
