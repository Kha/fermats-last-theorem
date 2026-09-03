import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range
    (O : Type*) [Ring O] [IsDomain O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hrank : Module.finrank ℤ O = 4)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ])) :
    Module.finrank ℚ (ℚ ⊗[ℤ] O) = 4 ∧
      (∀ x : ℚ ⊗[ℤ] O, x ≠ 0 → IsUnit x) ∧
      (∀ z : ℚ ⊗[ℤ] O, (∀ x : ℚ ⊗[ℤ] O, z * x = x * z) →
        z ∈ Set.range (algebraMap ℚ (ℚ ⊗[ℤ] O))) := by p2m_exact_reverting @_root_.P2MW.S_finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range.solution
