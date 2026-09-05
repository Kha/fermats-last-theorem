module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_deg_ne_zero

@[expose] public section

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.deg_ne_zero {K : Type*} [Field K] (v : Place K (RatFunc K)) : v.deg ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ne_zero.solution
