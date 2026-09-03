import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField
theorem QuaternionAlgebra.relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral
    {a b : ℚ} (hab : a ≠ 0 ∧ b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (A : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hA : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ A ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hki : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ)
    (n : ℕ) (B : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hB : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ B ↔
      (∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ) ∧
        ∀ i j, (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n)⁻¹] *
          ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ z *
          (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
          Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n]) i j ∈ v.adicCompletionIntegers ℚ) :
    B.relIndex A = ℓ ^ n := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral.solution
