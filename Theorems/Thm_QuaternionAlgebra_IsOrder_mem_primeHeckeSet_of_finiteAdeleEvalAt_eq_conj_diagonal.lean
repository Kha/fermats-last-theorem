import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_conj_diagonal

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField
theorem QuaternionAlgebra.IsOrder.mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_conj_diagonal
    {a b : ℚ} (hab : a ≠ 0 ∧ b ≠ 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (h₁ : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      z ∈ Submodule.localBox Λ v ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (k₁ k₂ : GL (Fin 2) (v.adicCompletion ℚ))
    (hk₁ : ∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hk₁i : ∀ i j, ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ)
    (hk₂ : ∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hk₂i : ∀ i j, ((k₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ)
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hsv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (s : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      φ.symm ((k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : ℕ) : v.adicCompletion ℚ)] *
        (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))))
    (hsw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (s : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) :
    s ∈ primeHeckeSet Λ ℓ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_conj_diagonal.solution
