import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem AlgebraicClosure.exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, τ x = x) →
        PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one.solution
