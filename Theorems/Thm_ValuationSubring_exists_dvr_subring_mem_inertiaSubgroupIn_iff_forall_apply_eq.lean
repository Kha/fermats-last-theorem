import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
attribute [-instance] AlgebraicClosure.Rat.isGalois

theorem ValuationSubring.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((ℓ : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) :
    ∃ O : Subring (AlgebraicClosure ℚ),
      (O : Set (AlgebraicClosure ℚ)) ⊆ A ∧
      (∀ r : ℚ, r.den.Coprime ℓ → algebraMap ℚ (AlgebraicClosure ℚ) r ∈ O) ∧
      IsDiscreteValuationRing ↥O ∧ Irreducible ((ℓ : ℕ) : ↥O) ∧
      (∀ x : ↥O, A.valuation (x : AlgebraicClosure ℚ) < 1 → ¬ IsUnit x) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x) ∧
      ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → y ∈ O := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq.solution
