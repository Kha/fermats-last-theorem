import Mathlib
import Definitions.Def_EllipticCurve_FifteenA1
import P2M.Util
import P2M.Sol.S_ModularCurve_FifteenA1_deltaPairHom

open ModularCurve.FifteenA1
theorem ModularCurve.FifteenA1.deltaPairHom (P Q : shortW.Point) : IsSqClass ((deltaPair P).1 * (deltaPair Q).1) (deltaPair (P + Q)).1 ∧ IsSqClass ((deltaPair P).2 * (deltaPair Q).2) (deltaPair (P + Q)).2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FifteenA1_deltaPairHom.solution
