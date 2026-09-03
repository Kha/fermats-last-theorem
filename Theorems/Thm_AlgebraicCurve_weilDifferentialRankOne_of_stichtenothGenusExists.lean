import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_weilDifferentialRankOne_of_stichtenothGenusExists

namespace AlgebraicCurve
theorem weilDifferentialRankOne_of_stichtenothGenusExists {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    (h : StichtenothGenusExists K F) : WeilDifferentialRankOne K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_weilDifferentialRankOne_of_stichtenothGenusExists.solution
end AlgebraicCurve
