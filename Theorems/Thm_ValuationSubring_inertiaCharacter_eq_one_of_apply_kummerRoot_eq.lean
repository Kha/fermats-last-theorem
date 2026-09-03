import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_inertiaCharacter_eq_one_of_apply_kummerRoot_eq

set_option autoImplicit false
theorem ValuationSubring.inertiaCharacter_eq_one_of_apply_kummerRoot_eq {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {n : ℕ} (hn0 : 0 < n) (hn : n.Coprime q) (α : AlgebraicClosure ℚ) (hα : α ^ n = (q : AlgebraicClosure ℚ))
    {A : Type} [CommGroup A] (ξ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → A)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hexp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ξ σ ^ n = 1)
    (hcont : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ x ∈ L, σ x = x) → ξ σ = 1)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hfix : σ α = α) :
    ξ σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_inertiaCharacter_eq_one_of_apply_kummerRoot_eq.solution
