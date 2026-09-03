import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField
theorem Matrix.GeneralLinearGroup.exists_eq_smul_mul_diagonal_mul_of_valuationSubring
    {K : Type*} [Field K] (O : ValuationSubring K) (H : GL (Fin 2) K) :
    ∃ (s t : K) (k₁ k₂ : GL (Fin 2) K), s ≠ 0 ∧ t ≠ 0 ∧ t ∈ O ∧
      (∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, ((k₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, ((k₂⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (H : Matrix (Fin 2) (Fin 2) K) =
        s • ((k₁ : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal ![(1 : K), t] * (k₂ : Matrix (Fin 2) (Fin 2) K)) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring.solution
