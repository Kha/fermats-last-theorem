import Mathlib.FieldTheory.KrullTopology
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd

theorem ResidualGaloisRep.restrict_index_two_of_isIrreducible_of_isOdd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (ρ : ResidualGaloisRep (ZMod p))
    (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd)
    (hnoext : ∀ H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        A.inertiaSubgroupIn ℚ ≤ H) → H = ⊤)
    (hq : ∀ q : ℕ, q.Prime → q ≠ p → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, (ρ.ρ σ - 1) * (ρ.ρ σ - 1) = 0)
    (hcyc : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∀ a : (ZMod p)ˣ, ∃ σ ∈ A.inertiaSubgroupIn ℚ, LinearMap.det (ρ.ρ σ) = a)
    (hp_local :
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∃ L : Submodule (ZMod p) ρ.V, L ≠ ⊤ ∧
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) ∨
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        (∃ W : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ, σ * τ * σ⁻¹ * τ⁻¹ ∈ W) ∧
          (∀ σ ∈ W, ∃ n : ℕ, ρ.ρ σ ^ p ^ n = 1)) ∧
        p ^ 2 - 1 ∣ Nat.card (ρ.ρ '' (A.inertiaSubgroupIn ℚ :
          Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))))
    (h3 : p = 3 →
      (∀ q : ℕ, q.Prime → q ≠ p → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ.ρ σ = 1) →
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        Nat.card (ρ.ρ '' (A.inertiaSubgroupIn ℚ :
          Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) ≤ 2) →
      Nat.card (Set.range ρ.ρ) ≤ 2)
    (K : Type) [Field K] [Algebra (ZMod p) K]
    (H₀ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hH₀ : H₀.index = 2)
    (ℓ : Submodule K (ρ.baseChange K).V)
    (hℓ : ∀ σ ∈ H₀, ∀ x ∈ ℓ, (ρ.baseChange K).ρ σ x ∈ ℓ) :
    ℓ = ⊥ ∨ ℓ = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd.solution
