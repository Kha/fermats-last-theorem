module

public import Definitions.Def_ModularCurve_AtkinLehner
public import Theorems.Thm_ModularCurve_ord_cuspInftyBar
public import Theorems.Thm_ModularCurve_order_coeffEmb
public import Theorems.Thm_ModularCurve_order_qExpand
public import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (d : ℕ) [NeZero d] (hd : d ∣ N) :
    (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hd)⟩ = -d := by
  rw [ModularCurve.ord_cuspInftyBar]
  change (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq)).order = _
  rw [ModularCurve.order_coeffEmb, ModularCurve.order_qExpand, order_jq, mul_neg, mul_one]
