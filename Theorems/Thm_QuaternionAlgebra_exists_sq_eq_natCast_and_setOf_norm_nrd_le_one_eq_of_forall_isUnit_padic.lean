import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_sq_eq_natCast_and_setOf_norm_nrd_le_one_eq_of_forall_isUnit_padic

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_sq_eq_natCast_and_setOf_norm_nrd_le_one_eq_of_forall_isUnit_padic
    (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (hD : ∀ x : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])], x ≠ 0 → IsUnit x)
    (t n : ℤ) (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0)
    (hN : ∀ u : ℤ_[p], IsUnit u → ∃ c d : ℤ_[p], c ^ 2 + (t : ℤ_[p]) * c * d + (n : ℤ_[p]) * d ^ 2 = u)
    (θ : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])])
    (hθ : θ * θ - (t : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) * θ + (n : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) = 0) :
    ∃ ϖ : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])],
      ϖ * ϖ = (p : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) ∧
      ϖ * θ = ((t : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) - θ) * ϖ ∧
      QuaternionAlgebra.trd θ = (t : ℚ_[p]) ∧ QuaternionAlgebra.nrd θ = (n : ℚ_[p]) ∧
      QuaternionAlgebra.trd ϖ = 0 ∧ QuaternionAlgebra.trd (θ * ϖ) = 0 ∧
      (∀ c₀ c₁ c₂ c₃ : ℚ_[p],
        (c₀ : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) + (c₁ : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) * θ
          + (c₂ : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) * ϖ + (c₃ : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) * (θ * ϖ) = 0 →
        c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0) ∧
      (∀ m : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])],
        ‖QuaternionAlgebra.nrd m‖ ≤ 1 ↔
          ∃ c₀ c₁ c₂ c₃ : ℤ_[p],
            m = ((c₀ : ℚ_[p]) : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) + ((c₁ : ℚ_[p]) : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) * θ
              + ((c₂ : ℚ_[p]) : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) * ϖ
              + ((c₃ : ℚ_[p]) : ℍ[ℚ_[p], (a : ℚ_[p]), (b : ℚ_[p])]) * (θ * ϖ)) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_sq_eq_natCast_and_setOf_norm_nrd_le_one_eq_of_forall_isUnit_padic.solution
