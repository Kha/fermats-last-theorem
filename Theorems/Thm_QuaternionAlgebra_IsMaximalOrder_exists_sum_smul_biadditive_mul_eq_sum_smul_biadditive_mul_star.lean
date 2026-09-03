import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_sum_smul_biadditive_mul_eq_sum_smul_biadditive_mul_star

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

universe u

theorem QuaternionAlgebra.IsMaximalOrder.exists_sum_smul_biadditive_mul_eq_sum_smul_biadditive_mul_star
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ) :
    ∃ (n : ℕ) (w : Fin n → ↥Λ) (m : Fin n → ℕ),
      0 < n ∧ (∀ i, 0 < m i) ∧ (∀ i, (w i : ℍ[ℚ, a, b]) ≠ 0) ∧
      ∀ (G : Type u) [AddCommGroup G] (β : ↥Λ →+ ↥Λ →+ G) (x : ↥Λ),
        ∑ i, m i • β (w i) ⟨(w i : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (w i).2 x.2⟩ =
        ∑ i, m i • β ⟨(w i : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (w i).2 (star x).2⟩ (w i) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_sum_smul_biadditive_mul_eq_sum_smul_biadditive_mul_star.solution
