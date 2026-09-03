import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import P2M.Util
import P2M.Sol.S_ExtCitation_liesOverPrime_primeLocalPlace

open ExtCitation
theorem ExtCitation.liesOverPrime_primeLocalPlace (q : Nat.Primes) : (primeLocalPlace q).LiesOverPrime q := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_liesOverPrime_primeLocalPlace.solution
