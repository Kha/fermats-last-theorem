module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_isCusp_cuspInftyBar

@[expose] public section

open ModularCurve AlgebraicCurve

theorem ModularCurve.isCusp_cuspInftyBar (N : ℕ) [NeZero N] : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (cuspInftyBar N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isCusp_cuspInftyBar.solution
