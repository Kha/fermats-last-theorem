import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_dvr_subring_of_forall_mem_decompositionSubgroup

open scoped Pointwise

theorem ValuationSubring.exists_dvr_subring_of_forall_mem_decompositionSubgroup
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((ℓ : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (S : Finset (AlgebraicClosure ℚ))
    (hS : ∀ x ∈ S, x ∈ A ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.decompositionSubgroup ℚ → σ x = x) :
    ∃ O : Subring (AlgebraicClosure ℚ),
      (↑S : Set (AlgebraicClosure ℚ)) ⊆ O ∧ (O : Set (AlgebraicClosure ℚ)) ⊆ A ∧
      (∀ q : ℚ, q.den.Coprime ℓ → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ O) ∧
      IsDiscreteValuationRing O ∧ Irreducible ((ℓ : ℕ) : O) ∧
      ∀ x : O, A.valuation (x : AlgebraicClosure ℚ) < 1 → ¬ IsUnit x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_dvr_subring_of_forall_mem_decompositionSubgroup.solution
