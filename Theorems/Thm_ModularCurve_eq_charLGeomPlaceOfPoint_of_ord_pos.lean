module

public import Mathlib
public import Definitions.Def_ModularCurve_SpecializeModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos

@[expose] public section
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open AlgebraicCurve ModularCurve
theorem ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos
    {k : Type*} [Field k] {v : Place k ↥(modularFunctionFieldC k 1)} {c : k}
    (h : 0 < v.ord ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
      - algebraMap k (modularFunctionFieldC k 1) c)) :
    v = charLGeomPlaceOfPoint k c := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos.solution
