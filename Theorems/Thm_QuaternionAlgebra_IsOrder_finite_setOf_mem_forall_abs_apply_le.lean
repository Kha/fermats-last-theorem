import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_finite_setOf_mem_forall_abs_apply_le

set_option autoImplicit false

open scoped MatrixGroups Quaternion
open QuaternionAlgebra CerednikDrinfeld
theorem QuaternionAlgebra.IsOrder.finite_setOf_mem_forall_abs_apply_le
    {a b : ℚ} (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (C : ℝ) :
    Set.Finite {α : ℍ[ℚ, a, b] | α ∈ Λ ∧ ∀ i j : Fin 2, |ι α i j| ≤ C} := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_finite_setOf_mem_forall_abs_apply_le.solution
