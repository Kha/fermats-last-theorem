import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_one_le_deg

namespace AlgebraicCurve
theorem one_le_deg {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] (P : Place K F) : 1 ≤ P.deg := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_one_le_deg.solution
end AlgebraicCurve
