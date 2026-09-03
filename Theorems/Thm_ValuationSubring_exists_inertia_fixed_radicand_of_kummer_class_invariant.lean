import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_inertia_fixed_radicand_of_kummer_class_invariant

set_option autoImplicit false
theorem ValuationSubring.exists_inertia_fixed_radicand_of_kummer_class_invariant
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N n : ℕ) (hn : n ≤ N)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (x : AlgebraicClosure ℚ) (hx0 : x ≠ 0)
    (hxfix : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → σ ξ = ξ) → σ x = x)
    (hinv : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ w : AlgebraicClosure ℚ,
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) → τ w = w) ∧ σ x = x * w ^ p ^ n) :
    ∃ x' w' : AlgebraicClosure ℚ, x' ≠ 0 ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x' = x') ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) → τ w' = w') ∧
      x = x' * w' ^ p ^ n := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_inertia_fixed_radicand_of_kummer_class_invariant.solution
