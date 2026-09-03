import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_mem_localBox_iff_forall_rTensor_entryLinearMap_comp_mem_localBox

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsOrder.mem_localBox_iff_forall_rTensor_entryLinearMap_comp_mem_localBox
    {a₁ b₁ c d : ℚ} {n : Type} [Fintype n] [DecidableEq n]
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix n n ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : QuaternionAlgebra.IsOrder O)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : n, τ x i l ∈ O)
    (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) :
    x ∈ Submodule.localBox R w ↔
      ∀ i l : n,
        ((Matrix.entryLinearMap ℚ ℍ[ℚ, c, d] i l ∘ₗ τ.toLinearMap).rTensor (w.adicCompletion ℚ)) x ∈
          Submodule.localBox O w := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_mem_localBox_iff_forall_rTensor_entryLinearMap_comp_mem_localBox.solution
