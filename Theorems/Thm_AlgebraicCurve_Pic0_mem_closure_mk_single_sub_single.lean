import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single
set_option autoImplicit false
open AlgebraicCurve

theorem AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single
    {K F : Type*} [Field K] [Field F] [Algebra K F] (h1 : ∀ v : Place K F, v.deg = 1)
    (V₀ : Place K F) (x : Pic0 K F) :
    x ∈ AddSubgroup.closure
      {y : Pic0 K F | ∃ (V : Place K F)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single.solution
