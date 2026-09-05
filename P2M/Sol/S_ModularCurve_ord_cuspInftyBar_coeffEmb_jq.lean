module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Sol.S_ModularCurve_ord_cuspInftyBar
import P2M.Util

namespace P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] :
    (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -1 := by
  rw [ModularCurve.ord_cuspInftyBar]
  exact order_coeffEmb_jq (AlgebraicClosure ℚ)
end S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
end P2MW

public section
open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspInftyBar_coeffEmb_jq (N : ℕ) [NeZero N] : (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq.solution
end
