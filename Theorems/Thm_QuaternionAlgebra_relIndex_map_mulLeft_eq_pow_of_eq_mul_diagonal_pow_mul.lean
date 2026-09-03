import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_relIndex_map_mulLeft_eq_pow_of_eq_mul_diagonal_pow_mul

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField

theorem QuaternionAlgebra.relIndex_map_mulLeft_eq_pow_of_eq_mul_diagonal_pow_mul
    {a b : ℚ} (hab : a ≠ 0 ∧ b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (A : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hA : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ A ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (k₁ k₂ : GL (Fin 2) (v.adicCompletion ℚ))
    (hk₁ : ∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hk₁i : ∀ i j, ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ)
    (hk₂ : ∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hk₂i : ∀ i j, ((k₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ)
    (e₁ e₂ : ℕ) (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
    (hg : φ g = (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
      Matrix.diagonal ![((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₁, ((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₂] * (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) :
    (A.map (AddMonoidHom.mulLeft g)).relIndex A = ℓ ^ (2 * (e₁ + e₂)) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_relIndex_map_mulLeft_eq_pow_of_eq_mul_diagonal_pow_mul.solution
