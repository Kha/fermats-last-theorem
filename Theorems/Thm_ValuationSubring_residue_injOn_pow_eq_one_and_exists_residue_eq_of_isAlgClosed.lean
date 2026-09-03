import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    (m : ℕ) (hm : (m : ResidueField ↥A) ≠ 0) :
    (∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂) ∧
    (∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed.solution
