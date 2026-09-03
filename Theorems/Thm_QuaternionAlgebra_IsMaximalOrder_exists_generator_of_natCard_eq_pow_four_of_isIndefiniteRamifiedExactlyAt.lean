import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_generator_of_natCard_eq_pow_four_of_isIndefiniteRamifiedExactlyAt
attribute [-simp] QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_generator_of_natCard_eq_pow_four_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (r : ℕ) (hr : r = q ∨ r = q')
    (M : Type) [AddCommGroup M] [Finite M] (hM : Nat.card M = r ^ 4) (hrM : ∀ P : M, r • P = 0)
    (ρ : ↥Λ → M →+ M)
    (ρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = AddMonoidHom.id M)
    (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    (hfaith : ∃ (P : M) (x : ↥Λ), (∃ n : ℤ, nrd (x : ℍ[ℚ, a, b]) = (r : ℚ) * n) ∧ ρ x P ≠ 0) :
    ∃ P₀ : M, (∀ P : M, ∃ m : ↥Λ, P = ρ m P₀) ∧
      (∀ m : ↥Λ, ρ m P₀ = 0 ↔ ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((r : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_generator_of_natCard_eq_pow_four_of_isIndefiniteRamifiedExactlyAt.solution
