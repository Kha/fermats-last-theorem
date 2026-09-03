import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single_of_notMem

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single_of_notMem
    {K : Type*} [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (S : Finset (Place K F)) (V₀ : Place K F) (hV₀ : V₀ ∉ S) (x : Pic0 K F) :
    x ∈ AddSubgroup.closure
      {y : Pic0 K F | ∃ (V : Place K F) (_ : V ∉ S)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single_of_notMem.solution
