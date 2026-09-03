import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_FinFlatHopf_inertiaFixed_valuationSubring_dvr_fixer_le_inertia
attribute [-instance] AlgebraicClosure.Rat.isGalois

theorem FinFlatHopf.inertiaFixed_valuationSubring_dvr_fixer_le_inertia (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (B : Subring (AlgebraicClosure ℚ))
    (hB : ∀ x : AlgebraicClosure ℚ, x ∈ B ↔
      (x ∈ P ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x)) :
    ((p : B) ∈ nonunits B ∧ ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : Bˣ), x = u * (p : B) ^ k) ∧
    (∀ q : ℚ, q ∈ GaloisRep.ratLocalizedAt p → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ B) ∧
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ B, σ x = x) →
      σ ∈ P.inertiaSubgroupIn ℚ) := by p2m_exact_reverting @_root_.P2MW.S_FinFlatHopf_inertiaFixed_valuationSubring_dvr_fixer_le_inertia.solution
