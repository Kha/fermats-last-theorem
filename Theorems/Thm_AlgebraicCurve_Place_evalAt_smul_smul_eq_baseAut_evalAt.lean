import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_smul_smul_eq_baseAut_evalAt
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : SemilinearAut K F) (v : AlgebraicCurve.Place K F)
    (hv : v.IsRational) (hσv : (σ • v).IsRational) (f : F) :
    (σ • v).evalAt (σ • f) = SemilinearAut.baseAut σ (v.evalAt f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt.solution
