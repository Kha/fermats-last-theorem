import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField

theorem Matrix.GeneralLinearGroup.exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers
    (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Y : GL (Fin 2) (v.adicCompletion ℚ))
    (hY : ∀ i j, (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ (e₁ e₂ : ℕ) (k₁ k₂ : GL (Fin 2) (v.adicCompletion ℚ)), e₁ ≤ e₂ ∧
      (∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ i j, ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ) ∧
      (∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ i j, ((k₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ) ∧
      (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        Matrix.diagonal ![((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₁, ((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₂] * (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
      ((∀ i j, ((((ℓ : ℕ) : v.adicCompletion ℚ)⁻¹ • (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)) ↔ 1 ≤ e₁) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers.solution
