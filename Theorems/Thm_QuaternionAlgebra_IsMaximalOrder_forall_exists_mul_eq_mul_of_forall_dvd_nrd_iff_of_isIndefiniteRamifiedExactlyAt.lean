import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_forall_exists_mul_eq_mul_of_forall_dvd_nrd_iff_of_isIndefiniteRamifiedExactlyAt
attribute [-simp] QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.forall_exists_mul_eq_mul_of_forall_dvd_nrd_iff_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q')
    (π : ℍ[ℚ, a, b]) (hπ : π ∈ Λ)
    (hgen : ∀ m ∈ Λ, (∃ n : ℤ, nrd m = (r : ℚ) * n) ↔ ∃ l ∈ Λ, m = l * π) :
    (∀ x ∈ Λ, ∃ y ∈ Λ, π * x = y * π) ∧ (∀ x ∈ Λ, ∃ y ∈ Λ, x * π = π * y) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_exists_mul_eq_mul_of_forall_dvd_nrd_iff_of_isIndefiniteRamifiedExactlyAt.solution
