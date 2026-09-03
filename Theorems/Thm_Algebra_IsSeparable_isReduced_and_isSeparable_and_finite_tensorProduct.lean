import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsSeparable_isReduced_and_isSeparable_and_finite_tensorProduct

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.IsSeparable.isReduced_and_isSeparable_and_finite_tensorProduct
    (K₁ K E : Type*) [Field K₁] [Field K] [Field E] [Algebra K₁ K] [Algebra K₁ E]
    [FiniteDimensional K₁ K] [Algebra.IsSeparable K₁ K] :
    IsReduced (E ⊗[K₁] K) ∧ Algebra.IsSeparable E (E ⊗[K₁] K) ∧ Module.Finite E (E ⊗[K₁] K) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsSeparable_isReduced_and_isSeparable_and_finite_tensorProduct.solution
