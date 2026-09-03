import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic

theorem WittVector.exists_valuationSubring_residueField_equiv_of_isAlgebraic (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] (Ω : Type*) [Field Ω] [Algebra (WittVector p k) Ω] [FaithfulSMul (WittVector p k) Ω] [Algebra.IsAlgebraic (WittVector p k) Ω] : ∃ (V : ValuationSubring Ω) (hV : ∀ a : WittVector p k, algebraMap (WittVector p k) Ω a ∈ V) (φ : k ≃+* IsLocalRing.ResidueField V), (∀ a ∈ IsLocalRing.maximalIdeal (WittVector p k), algebraMap (WittVector p k) Ω a ∈ V.nonunits) ∧ ∀ a : WittVector p k, φ (a.coeff 0) = IsLocalRing.residue V ⟨algebraMap (WittVector p k) Ω a, hV a⟩ := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic.solution
