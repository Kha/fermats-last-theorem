import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_riemannGenusBounded_of_indexFinite

namespace AlgebraicCurve
theorem riemannGenusBounded_of_indexFinite {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hfin : IndexOfSpecialtyFinite K F) :
    RiemannGenusBounded K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_riemannGenusBounded_of_indexFinite.solution
end AlgebraicCurve
