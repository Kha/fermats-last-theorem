import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_existsUnique_forall_intCast_eq_trd_mul_of_isIndefiniteRamifiedExactlyAt

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.existsUnique_forall_intCast_eq_trd_mul_of_isIndefiniteRamifiedExactlyAt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (f : ↥Λ →ₗ[ℤ] ℤ) :
    ∃! c : ℍ[ℚ, a, b], ∀ y : ↥Λ, ((f y : ℤ) : ℚ) = trd (c * (y : ℍ[ℚ, a, b])) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_existsUnique_forall_intCast_eq_trd_mul_of_isIndefiniteRamifiedExactlyAt.solution
