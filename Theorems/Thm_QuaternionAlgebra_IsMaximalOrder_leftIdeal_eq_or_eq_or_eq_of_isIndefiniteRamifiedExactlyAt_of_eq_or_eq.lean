import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
attribute [-simp] QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :

    ((∀ m ∈ Λ, ∀ x ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) → ∃ n : ℤ, nrd (m * x) = (r : ℚ) * n) ∧
      (∀ y ∈ Λ, ∃ n : ℤ, nrd ((r : ℤ) • y) = (r : ℚ) * n) ∧
      (∃ x ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) ∧ ¬ ∃ y ∈ Λ, x = (r : ℤ) • y) ∧
      (∃ x ∈ Λ, ¬ ∃ n : ℤ, nrd x = (r : ℚ) * n) ∧

      (∀ x ∈ Λ, ∀ x' ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) → (∃ n : ℤ, nrd x' = (r : ℚ) * n) →
        ∃ y ∈ Λ, x * x' = (r : ℤ) • y)) ∧

    ∀ J : Submodule ℤ ℍ[ℚ, a, b], J ≤ Λ → (∀ y ∈ Λ, (r : ℤ) • y ∈ J) → (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) →
      (∀ x, x ∈ J ↔ ∃ y ∈ Λ, x = (r : ℤ) • y) ∨
      (∀ x, x ∈ J ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n) ∨
      J = Λ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq.solution
