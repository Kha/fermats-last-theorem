module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_Pic0_mk_eq_zero_iff

@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.mk_eq_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_mk_eq_zero_iff.solution
