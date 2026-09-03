import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_natCard_properLine_eq_and_inf_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry open QuaternionAlgebra hiding exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne open CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem QuaternionAlgebra.IsMaximalOrder.natCard_properLine_eq_and_inf_eq
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
        (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ} = ℓ + 1 ∧
    ∀ J J' : Submodule ℤ ℍ[ℚ, a, b],
      J ≤ Λ → (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) → (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) →
      J' ≤ Λ → (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J') → (∀ m ∈ Λ, ∀ x ∈ J', m * x ∈ J') →
      J ≠ Λ → J' ≠ Λ → J ≠ J' →
      ∀ x : ℍ[ℚ, a, b], x ∈ J → x ∈ J' → ∃ y ∈ Λ, x = (ℓ : ℤ) • y := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_properLine_eq_and_inf_eq.solution
