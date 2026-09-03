import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isTraceDiff_traceDiff

theorem AlgebraicCurve.isTraceDiff_traceDiff (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] : IsTraceDiff K F F' (traceDiff K F F') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isTraceDiff_traceDiff.solution
