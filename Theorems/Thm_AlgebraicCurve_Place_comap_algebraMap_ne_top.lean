import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_comap_algebraMap_ne_top
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.comap_algebraMap_ne_top {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F'] (w : Place K F') [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_comap_algebraMap_ne_top.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.comap_algebraMap_ne_top AlgebraicCurve.Place.comap_algebraMap_ne_top
