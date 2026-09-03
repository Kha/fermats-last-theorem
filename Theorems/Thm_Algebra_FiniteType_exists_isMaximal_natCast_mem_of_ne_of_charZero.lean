import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero

set_option autoImplicit false

open scoped MatrixGroups
theorem Algebra.FiniteType.exists_isMaximal_natCast_mem_of_ne_of_charZero
    (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] :
    ∃ (p₁ p₂ : ℕ) (𝔪₁ 𝔪₂ : Ideal A), p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧ 𝔪₁.IsMaximal ∧ 𝔪₂.IsMaximal ∧
      (p₁ : A) ∈ 𝔪₁ ∧ (p₂ : A) ∈ 𝔪₂ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero.solution
