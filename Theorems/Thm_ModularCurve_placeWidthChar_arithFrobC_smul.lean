import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import P2M.Util
import P2M.Sol.S_ModularCurve_placeWidthChar_arithFrobC_smul
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.placeWidthChar_arithFrobC_smul
    (q N : ℕ) [Fact q.Prime] [NeZero N]
    {K : Type*} [Field K] [CharP K q] [PerfectField K] [DecidableEq K]
    (w : Place K (modularFunctionFieldC K N)) :
    placeWidthChar q N (arithFrobC q K N • w) = placeWidthChar q N w := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_placeWidthChar_arithFrobC_smul.solution
