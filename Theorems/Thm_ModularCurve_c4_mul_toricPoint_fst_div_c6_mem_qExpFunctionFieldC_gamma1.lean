import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1

open ModularCurve WeierstrassCurve

universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 ζ).1) / (tateLaurent K).c₆ ∈
        qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) ∧
      ((toricPoint K 1 ζ).1 + 6 * (toricPoint K 1 ζ).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄ ∈
        qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1.solution
