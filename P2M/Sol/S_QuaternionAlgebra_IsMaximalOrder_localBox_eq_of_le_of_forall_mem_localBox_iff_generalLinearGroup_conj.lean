import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_isOrder_le_localBox_iff_conj_apply_mem_adicCompletionIntegers
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_localBox_eq_of_le_of_forall_mem_localBox_iff_generalLinearGroup_conj

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem solution
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
    Submodule.localBox Λ₁ v = Submodule.localBox Λ₂ v := by
  obtain ⟨Λ', hΛ', hle', hbox⟩ :=
    QuaternionAlgebra.IsOrder.exists_isOrder_le_localBox_iff_conj_apply_mem_adicCompletionIntegers
      hΛ₁.isOrder v φ hφ H (fun x hx => (h₂ x).1 (hle hx))
  obtain rfl : Λ' = Λ₁ := hΛ₁.2 Λ' hΛ' hle'
  exact le_antisymm hle fun x hx => (hbox x).2 ((h₂ x).1 hx)
