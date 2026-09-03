import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range
    (k : Type u) (F : Type v) (K : Type w) [Field k] [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra.IsSeparable k K]
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range) :
    IsField (F ⊗[k] K) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.solution
