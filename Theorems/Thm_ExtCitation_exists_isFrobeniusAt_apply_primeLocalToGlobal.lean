import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
attribute [-instance] instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete

open ExtCitation
theorem ExtCitation.exists_isFrobeniusAt_apply_primeLocalToGlobal (q : Nat.Primes) :
    ∃ φ : primeLocalGaloisGroup q, (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal.solution
