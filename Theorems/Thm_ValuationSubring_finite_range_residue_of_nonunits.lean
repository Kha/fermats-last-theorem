import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_finite_range_residue_of_nonunits

theorem ValuationSubring.finite_range_residue_of_nonunits
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K L] :
    (Set.range fun x : {x : AlgebraicClosure ℚ // x ∈ L ∧ x ∈ A} =>
      IsLocalRing.residue ↥A ⟨x.1, x.2.2⟩).Finite := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_finite_range_residue_of_nonunits.solution
