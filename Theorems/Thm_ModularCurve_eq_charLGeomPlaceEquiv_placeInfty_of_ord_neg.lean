module

public import Mathlib
public import Definitions.Def_ModularCurve_SpecializeModuli
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import P2M.Util
import P2M.Sol.S_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg

@[expose] public section

open AlgebraicCurve ModularCurve
theorem ModularCurve.eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
    {k : Type*} [Field k] [DecidableEq (RatFunc k)] {v : Place k ↥(modularFunctionFieldC k 1)}
    (h : v.ord ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)) < 0) :
    v = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg.solution
