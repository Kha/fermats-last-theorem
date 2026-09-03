import Definitions.Def_FLTPrelim_Ramification
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside

open NumberField IsDedekindDomain
theorem AlgebraicClosure.exists_uniform_level_of_characters_unramified_outside
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L'] (p₀ : ℕ) (hp₀ : p₀.Prime)
    (S : Finset ℕ) :
    ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧ L' ≤ M ∧
      ∀ χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ZMod p₀,
        (∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          σ ∈ L'.fixingSubgroup → τ ∈ L'.fixingSubgroup → χ (σ * τ) = χ σ + χ τ) →
        (∃ L₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L₀ ∧
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ L₀.fixingSubgroup → χ σ = 0) →
        (∀ q : ℕ, q.Prime → q ∉ S → ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ ∈ L'.fixingSubgroup → χ σ = 0) →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ M.fixingSubgroup → χ σ = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside.solution
