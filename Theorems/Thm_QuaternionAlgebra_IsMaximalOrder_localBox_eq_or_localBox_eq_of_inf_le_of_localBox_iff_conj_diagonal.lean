import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_localBox_eq_or_localBox_eq_of_inf_le_of_localBox_iff_conj_diagonal

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsMaximalOrder.localBox_eq_or_localBox_eq_of_inf_le_of_localBox_iff_conj_diagonal
    {a b : ℚ} {Λ₁ Λ₂ Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) (hle : Λ₁ ⊓ Λ₂ ≤ Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (h : GL (Fin 2) (v.adicCompletion ℚ))
    (h₁ : ∀ x, x ∈ Submodule.localBox Λ₁ v ↔ ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)
    (h₂ : ∀ x, x ∈ Submodule.localBox Λ₂ v ↔ ∀ i j,
      (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (ℓ : v.adicCompletion ℚ)⁻¹] *
        ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), (ℓ : v.adicCompletion ℚ)]) i j
          ∈ v.adicCompletionIntegers ℚ) :
    Submodule.localBox Λ v = Submodule.localBox Λ₁ v ∨ Submodule.localBox Λ v = Submodule.localBox Λ₂ v := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_localBox_eq_or_localBox_eq_of_inf_le_of_localBox_iff_conj_diagonal.solution
