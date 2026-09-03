import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq
attribute [-instance] CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction
attribute [-simp] QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {p : ℕ} [Fact p.Prime] (hp : p = q ∨ p = q') :
    ∃ (ω : ℍ[ℚ, a, b]) (hω : ω ∈ Λ) (t n : ℤ),

      ω + Star.star ω = ((t : ℚ) : ℍ[ℚ, a, b]) ∧
      ω * Star.star ω = ((n : ℚ) : ℍ[ℚ, a, b]) ∧
      (∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0) ∧
      ((t : ZMod p) ^ 2 - 4 * (n : ZMod p) ≠ 0) ∧

      (∃ z : ℍ[ℚ, a, b], z ∈ Λ ∧
        (μ : ℍ[ℚ, a, b]) * ω + ω * μ - (t : ℚ) • (μ : ℍ[ℚ, a, b]) = (p : ℚ) • z) ∧

      (∃ (c₀ c₁ : ℤ) (y : ℍ[ℚ, a, b]), y ∈ Λ ∧
        (star ⟨ω, hω⟩ : ℍ[ℚ, a, b]) - ω =
          (μ : ℍ[ℚ, a, b]) * (((c₀ : ℚ) : ℍ[ℚ, a, b]) + (c₁ : ℚ) • ω) + (p : ℚ) • y) ∧

      (∃ (l₁ l₂ : ℍ[ℚ, a, b]), l₁ ∈ Λ ∧ l₂ ∈ Λ ∧
        (star ⟨ω, hω⟩ : ℍ[ℚ, a, b]) = ω + (p : ℚ) • l₁ + (μ : ℍ[ℚ, a, b]) * l₂) ∧

      (star μ : ℍ[ℚ, a, b]) = -(μ : ℍ[ℚ, a, b]) ∧
      (∀ x : ↥Λ, star (star x) = x) ∧
      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, star ⟨1, h1⟩ = ⟨1, h1⟩) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq.solution
