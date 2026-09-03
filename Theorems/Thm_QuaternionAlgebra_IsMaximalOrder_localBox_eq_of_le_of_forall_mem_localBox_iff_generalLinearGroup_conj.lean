import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_localBox_eq_of_le_of_forall_mem_localBox_iff_generalLinearGroup_conj

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField
theorem QuaternionAlgebra.IsMaximalOrder.localBox_eq_of_le_of_forall_mem_localBox_iff_generalLinearGroup_conj
    {a b : ℚ} {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (H : GL (Fin 2) (v.adicCompletion ℚ))
    (h₂ : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox Λ₂ v ↔
        ∀ i j, (((H⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
          φ x * (H : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)
    (hle : Submodule.localBox Λ₁ v ≤ Submodule.localBox Λ₂ v) :
    Submodule.localBox Λ₁ v = Submodule.localBox Λ₂ v := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_localBox_eq_of_le_of_forall_mem_localBox_iff_generalLinearGroup_conj.solution
