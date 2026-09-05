module

public import Definitions.Def_AlgebraicCurve_PlacesOverDVR
public import Mathlib.FieldTheory.RatFunc.Basic
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional

@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.finite_setOf_ord_ne_zero_of_finiteDimensional {K F' : Type*} [Field K] [Field F'] [Algebra K F']
    [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']
    {f : F'} (hf : f ≠ 0) : {w : Place K F' | w.ord f ≠ 0}.Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional.solution
