import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_finite_isUnitOf_and_nrd_eq_one

open scoped Quaternion
theorem QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one
    {a b : ℚ} (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) :
    Finite {u : ℍ[ℚ, a, b] // QuaternionAlgebra.IsUnitOf Λ u} ∧
      ∀ u : ℍ[ℚ, a, b], QuaternionAlgebra.IsUnitOf Λ u → QuaternionAlgebra.nrd u = 1 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_finite_isUnitOf_and_nrd_eq_one.solution
