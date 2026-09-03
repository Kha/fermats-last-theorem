import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_nonunits

theorem ValuationSubring.exists_algEquiv_forall_mem_iff_of_nonunits
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A A'' : ValuationSubring (AlgebraicClosure ℚ))
    (hle : ∀ x : AlgebraicClosure ℚ, x ∈ K → x ∈ A → x ∈ A'')
    {q : ℕ} (hq : q.Prime)
    (hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) (hqA'' : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A''.nonunits)
    (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K L] :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ,
      ∀ x : AlgebraicClosure ℚ, x ∈ L → (x ∈ A'' ↔ τ x ∈ A) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_nonunits.solution
