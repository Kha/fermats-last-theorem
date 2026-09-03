import Mathlib
import P2M.Util
import P2M.Sol.S_TensorProduct_AlgebraTensorModule_cancelBaseChange_baseChange_baseChange_apply

open scoped TensorProduct

theorem TensorProduct.AlgebraTensorModule.cancelBaseChange_baseChange_baseChange_apply
    (q : ℕ) [Fact q.Prime] (Λ : Type) [AddCommGroup Λ] (f : Λ →ₗ[ℤ] Λ)
    (x : ℚ_[q] ⊗[ℤ_[q]] (ℤ_[q] ⊗[ℤ] Λ)) :
    cancelBaseChange ℤ ℤ_[q] ℚ_[q] ℚ_[q] Λ (((f.baseChange ℤ_[q]).baseChange ℚ_[q]) x) =
      (f.baseChange ℚ_[q]) (cancelBaseChange ℤ ℤ_[q] ℚ_[q] ℚ_[q] Λ x) := by p2m_exact_reverting @_root_.P2MW.S_TensorProduct_AlgebraTensorModule_cancelBaseChange_baseChange_baseChange_apply.solution
