import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal

theorem ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime]
    (hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (c : A) (hc : c ≠ 0) (c' : A) (hc' : c' ∈ IsLocalRing.maximalIdeal A) (hc'0 : c' ≠ 0) :
    ∃ M : ℕ, c ∣ c' ^ M := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal.solution
