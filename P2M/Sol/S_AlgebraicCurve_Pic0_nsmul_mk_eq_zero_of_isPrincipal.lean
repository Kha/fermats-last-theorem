module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Sol.S_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal
import P2M.Util

namespace P2MW.S_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℕ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := by
  have h := AlgebraicCurve.Pic0.zsmul_mk_eq_zero_of_isPrincipal D (m : ℤ) (by rwa [natCast_zsmul])
  rwa [natCast_zsmul] at h
end S_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.Pic0.nsmul_mk_eq_zero_of_isPrincipal {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℕ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal.solution
end
