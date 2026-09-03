import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem ExtCitation.cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    {σ : primeLocalGaloisGroup q}
    (hσ : σ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) :
    cycloChar p (primeLocalToGlobal q σ) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia.solution
