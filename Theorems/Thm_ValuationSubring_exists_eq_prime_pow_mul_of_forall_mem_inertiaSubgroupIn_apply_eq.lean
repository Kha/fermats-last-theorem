import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_eq_prime_pow_mul_of_forall_mem_inertiaSubgroupIn_apply_eq
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false
theorem ValuationSubring.exists_eq_prime_pow_mul_of_forall_mem_inertiaSubgroupIn_apply_eq
    (p : ℕ) (hp : p.Prime) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (x : AlgebraicClosure ℚ) (hx0 : x ≠ 0) (hxP : x ∈ P)
    (hxI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x) :
    ∃ (n : ℕ) (u : AlgebraicClosure ℚ), P.valuation u = 1 ∧ (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ u = u) ∧
      x = (p : AlgebraicClosure ℚ) ^ n * u := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_eq_prime_pow_mul_of_forall_mem_inertiaSubgroupIn_apply_eq.solution
