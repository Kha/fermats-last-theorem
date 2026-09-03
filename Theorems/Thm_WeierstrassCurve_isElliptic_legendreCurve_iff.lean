import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isElliptic_legendreCurve_iff

open WeierstrassCurve
theorem WeierstrassCurve.isElliptic_legendreCurve_iff {K : Type*} [Field K] (t : K) (h2 : (2 : K) ≠ 0) :
    (legendreCurve t).IsElliptic ↔ t ≠ 0 ∧ t ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isElliptic_legendreCurve_iff.solution
