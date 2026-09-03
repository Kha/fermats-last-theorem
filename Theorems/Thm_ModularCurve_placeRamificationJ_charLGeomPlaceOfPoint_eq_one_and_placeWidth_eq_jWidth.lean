import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SpecializeModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth
    {K : Type*} [Field K] [DecidableEq K] (a : K) :
    placeRamificationJ 1 (charLGeomPlaceOfPoint K a) = 1 ∧
    placeWidth 1 (charLGeomPlaceOfPoint K a) = jWidth a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth.solution
