import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf
    {a b : ℚ} (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) :
    (∀ u : ℍ[ℚ, a, b], QuaternionAlgebra.IsUnitOf Λ u → u ^ 12 = 1) ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card {u : ℍ[ℚ, a, b] // QuaternionAlgebra.IsUnitOf Λ u} := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf.solution
