import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Matrix_exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

theorem Matrix.exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring
    (v : HeightOneSpectrum (𝓞 ℚ))
    (O : Subring (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hsmul : ∀ r : v.adicCompletion ℚ, r ∈ v.adicCompletionIntegers ℚ → ∀ x ∈ O, r • x ∈ O)
    (hbdd : ∃ d : v.adicCompletion ℚ, d ≠ 0 ∧ ∀ x ∈ O, ∀ i j, d * x i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ h : GL (Fin 2) (v.adicCompletion ℚ), ∀ x ∈ O, ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * x *
        (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring.solution
