import Mathlib
import Definitions.Def_EllipticCurve_FifteenA1
import P2M.Util
import P2M.Sol.S_ModularCurve_FifteenA1_selmerBound

open ModularCurve.FifteenA1
theorem ModularCurve.FifteenA1.selmerBound (P : shortW.Point) : ∃ v ∈ V₀, IsSqClass v.1 (deltaPair P).1 ∧ IsSqClass v.2 (deltaPair P).2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FifteenA1_selmerBound.solution
