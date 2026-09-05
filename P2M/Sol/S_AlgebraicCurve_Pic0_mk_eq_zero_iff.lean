module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util

namespace P2MW.S_AlgebraicCurve_Pic0_mk_eq_zero_iff

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F) := by
  rw [show Pic0.mk D = QuotientAddGroup.mk D from rfl, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf]
  exact Divisor.mem_principal
end S_AlgebraicCurve_Pic0_mk_eq_zero_iff
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.Pic0.mk_eq_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_mk_eq_zero_iff.solution
end
