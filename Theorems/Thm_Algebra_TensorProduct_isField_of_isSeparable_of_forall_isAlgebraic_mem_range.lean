import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isAlgebraic_mem_range

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.TensorProduct.isField_of_isSeparable_of_forall_isAlgebraic_mem_range
    (k F K : Type*) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra.IsSeparable k K]
    (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range) :
    IsField (F ⊗[k] K) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isAlgebraic_mem_range.solution
