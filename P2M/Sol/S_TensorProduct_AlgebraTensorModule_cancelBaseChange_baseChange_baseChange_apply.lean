import Mathlib
import P2M.Util
namespace P2MW.S_TensorProduct_AlgebraTensorModule_cancelBaseChange_baseChange_baseChange_apply

open scoped TensorProduct

open TensorProduct.AlgebraTensorModule (cancelBaseChange cancelBaseChange_tmul) in

theorem solution
    (q : ℕ) [Fact q.Prime] (Λ : Type) [AddCommGroup Λ] (f : Λ →ₗ[ℤ] Λ)
    (x : ℚ_[q] ⊗[ℤ_[q]] (ℤ_[q] ⊗[ℤ] Λ)) :
    cancelBaseChange ℤ ℤ_[q] ℚ_[q] ℚ_[q] Λ (((f.baseChange ℤ_[q]).baseChange ℚ_[q]) x) =
      (f.baseChange ℚ_[q]) (cancelBaseChange ℤ ℤ_[q] ℚ_[q] ℚ_[q] Λ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b l =>
      simp [LinearMap.baseChange_tmul, cancelBaseChange_tmul]
    | add y z hy hz =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, hy, hz]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
