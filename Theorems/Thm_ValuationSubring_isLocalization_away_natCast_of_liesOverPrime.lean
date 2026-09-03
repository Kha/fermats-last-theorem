import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isLocalization_away_natCast_of_liesOverPrime

set_option autoImplicit false

open AlgebraicGeometry

theorem ValuationSubring.isLocalization_away_natCast_of_liesOverPrime
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) :
    IsLocalization.Away ((p : ℕ) : ↥O) (AlgebraicClosure ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isLocalization_away_natCast_of_liesOverPrime.solution
