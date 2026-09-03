import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_units_mem_localBox_nsmul_inv_mem_forall_mem_localBox_iff_of_generalLinearGroup_conj

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField
theorem QuaternionAlgebra.exists_units_mem_localBox_nsmul_inv_mem_forall_mem_localBox_iff_of_generalLinearGroup_conj
    {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (h₁ : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox Λ₁ v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)
    (H : GL (Fin 2) (v.adicCompletion ℚ))
    (h₂ : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox Λ₂ v ↔
        ∀ i j, (((H⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
          φ x * (H : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)
    (N : ℕ) (hN : ∀ x ∈ Submodule.localBox Λ₁ v, N • x ∈ Submodule.localBox Λ₂ v) :
    ∃ m : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      (m : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ₁ v ∧
      N • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈
        Submodule.localBox Λ₁ v ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox Λ₂ v ↔
          ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * x * m ∈
            Submodule.localBox Λ₁ v := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_units_mem_localBox_nsmul_inv_mem_forall_mem_localBox_iff_of_generalLinearGroup_conj.solution
