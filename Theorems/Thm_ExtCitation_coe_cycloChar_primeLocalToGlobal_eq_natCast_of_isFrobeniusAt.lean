import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem ExtCitation.coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    {φ : primeLocalGaloisGroup q}
    (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q) :
    ((cycloChar p (primeLocalToGlobal q φ) : (ZMod p)ˣ) : ZMod p) = ((q : ℕ) : ZMod p) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt.solution
