import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra hiding exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne open CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (t t' : ℍ[ℚ, a, b]) (ht : t ∈ Λ) (ht' : t' ∈ Λ) (hnt : nrd t = (ℓ : ℚ)) (hnt' : nrd t' = (ℓ : ℚ))
    (hlev : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x)
    (hlev' : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t' = x) ↔ ∃ j ∈ J', j * t' = x) :
    ∃ c ∈ Λ, (∃ k : ℤ, nrd c = 1 + (ℓ : ℚ) * (k : ℚ)) ∧
      (∀ y ∈ J', ∃ y'' ∈ J', ∃ z ∈ Λ, ((N : ℤ) • y) * c = (N : ℤ) • y'' + (ℓ : ℤ) • z) ∧
      (∀ m ∈ Λ, ∃ m' ∈ Λ, ∃ z ∈ Λ, m * t * c = m' * t' + (ℓ : ℤ) • z) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity.solution
