import Mathlib
import Definitions.Def_EllipticCurve_FifteenA1
import P2M.Util
import P2M.Sol.S_ModularCurve_FifteenA1_secondDescentInput

open ModularCurve.FifteenA1
theorem ModularCurve.FifteenA1.secondDescentInput (P : shortW.Point) (h1 : IsSqClass 1 (deltaPair P).1) (h2 : IsSqClass 1 (deltaPair P).2) : ∃ Q : shortW.Point, P = 2 • Q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FifteenA1_secondDescentInput.solution
