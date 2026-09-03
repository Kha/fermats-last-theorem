import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_degree_nonneg_of_nonneg

namespace AlgebraicCurve
theorem Divisor.degree_nonneg_of_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) : 0 ≤ Divisor.degree D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_degree_nonneg_of_nonneg.solution
end AlgebraicCurve
