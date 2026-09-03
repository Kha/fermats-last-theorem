import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_forall_exists_smul_add_mul_iff_mul_of_isUnitOf_right

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.forall_exists_smul_add_mul_iff_mul_of_isUnitOf_right
    {a b : ℚ} {N : ℕ} (Λ R J' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hRΛ : R ≤ Λ)
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (t v : ℍ[ℚ, a, b]) (ht : t ∈ R) (hv : v ∈ R)
    (hv' : ∃ v' : ℍ[ℚ, a, b], v' ∈ R ∧ v * v' = 1 ∧ v' * v = 1)
    (hlev : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) :
    t * v ∈ R ∧ nrd (t * v) = nrd t * nrd v ∧
      ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * (t * v) = x) ↔ ∃ j ∈ J', j * (t * v) = x := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_forall_exists_smul_add_mul_iff_mul_of_isUnitOf_right.solution
