import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_algEquiv_residue_pow_eq_of_nonunits

theorem ValuationSubring.exists_algEquiv_residue_pow_eq_of_nonunits
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K L] (m : ℕ)
    (hfix : ∀ (x : AlgebraicClosure ℚ) (hxK : x ∈ K) (hxA : x ∈ A),
      IsLocalRing.residue ↥A ⟨x, hxA⟩ ^ (q ^ m) = IsLocalRing.residue ↥A ⟨x, hxA⟩) :
    ∃ δ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ,
      (∀ x : AlgebraicClosure ℚ, x ∈ L → (x ∈ A ↔ δ x ∈ A)) ∧
      ∀ (x : AlgebraicClosure ℚ) (hxL : x ∈ L) (hxA : x ∈ A) (hδ : δ x ∈ A),
        IsLocalRing.residue ↥A ⟨δ x, hδ⟩ ^ (q ^ m) = IsLocalRing.residue ↥A ⟨x, hxA⟩ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_algEquiv_residue_pow_eq_of_nonunits.solution
