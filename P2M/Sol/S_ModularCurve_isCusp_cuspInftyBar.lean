module

public import Definitions.Def_ModularCurve_AtkinLehner
public import Theorems.Thm_ModularCurve_isCusp_iff_ord_neg
public import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_isCusp_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] :
    IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (cuspInftyBar N) := by
  rw [ModularCurve.isCusp_iff_ord_neg, ModularCurve.ord_cuspInftyBar_coeffEmb_jq]
  norm_num
