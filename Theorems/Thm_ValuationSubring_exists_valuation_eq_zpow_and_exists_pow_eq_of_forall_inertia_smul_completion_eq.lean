import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_valuation_eq_zpow_and_exists_pow_eq_of_forall_inertia_smul_completion_eq
attribute [-instance] AlgebraicClosure.Rat.isGalois
set_option autoImplicit false

theorem ValuationSubring.exists_valuation_eq_zpow_and_exists_pow_eq_of_forall_inertia_smul_completion_eq
    (p : ℕ) (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    (∀ x : A.valuation.Completion, x ≠ 0 →
        (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → σ • x = x) →
        ∃ n : ℤ, Valued.v x = Valued.v ((p : ℕ) : A.valuation.Completion) ^ n) ∧
      (∀ n : ℕ, ¬ p ∣ n → ∀ μ : A.valuation.Completion,
        (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → σ • μ = μ) → Valued.v μ = 1 →
        ∃ ρ : A.valuation.Completion,
          (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → σ • ρ = ρ) ∧ ρ ^ n = μ) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_valuation_eq_zpow_and_exists_pow_eq_of_forall_inertia_smul_completion_eq.solution
