module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors

@[expose] public section
open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.solution
