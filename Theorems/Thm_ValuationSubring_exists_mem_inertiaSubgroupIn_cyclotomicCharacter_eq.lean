import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
    (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} [Fact p.Prime] (hA : A.LiesOverPrime p)
    (u : ℤ_[p]ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ,
      cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv = u := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq.solution
