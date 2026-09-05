module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Sol.S_ModularCurve_isCusp_iff_ord_neg
import P2M.Sol.S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import P2M.Util

namespace P2MW.S_ModularCurve_isCusp_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] :
    IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (cuspInftyBar N) := by
  rw [ModularCurve.isCusp_iff_ord_neg, ModularCurve.ord_cuspInftyBar_coeffEmb_jq]
  norm_num
end S_ModularCurve_isCusp_cuspInftyBar
end P2MW

public section
open ModularCurve AlgebraicCurve

theorem ModularCurve.isCusp_cuspInftyBar (N : ℕ) [NeZero N] : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (cuspInftyBar N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isCusp_cuspInftyBar.solution
end
