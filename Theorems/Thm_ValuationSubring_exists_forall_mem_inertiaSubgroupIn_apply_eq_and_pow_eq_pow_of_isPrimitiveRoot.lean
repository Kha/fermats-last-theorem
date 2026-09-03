import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_forall_mem_inertiaSubgroupIn_apply_eq_and_pow_eq_pow_of_isPrimitiveRoot

set_option autoImplicit false

theorem ValuationSubring.exists_forall_mem_inertiaSubgroupIn_apply_eq_and_pow_eq_pow_of_isPrimitiveRoot
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N)) (w : AlgebraicClosure ℚ)
    (hw : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ ζ = ζ → σ w = w)
    (hx : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (w ^ p ^ N) = w ^ p ^ N) :
    ∃ w' : AlgebraicClosure ℚ, (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ w' = w') ∧ w' ^ p ^ N = w ^ p ^ N := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_mem_inertiaSubgroupIn_apply_eq_and_pow_eq_pow_of_isPrimitiveRoot.solution
