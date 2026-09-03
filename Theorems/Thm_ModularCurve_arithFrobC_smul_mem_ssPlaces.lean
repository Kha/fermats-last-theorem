import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import P2M.Util
import P2M.Sol.S_ModularCurve_arithFrobC_smul_mem_ssPlaces

theorem ModularCurve.arithFrobC_smul_mem_ssPlaces (q N : ℕ) [NeZero N] (K : Type) [Field K]
    [DecidableEq K] [Fact q.Prime] [CharP K q] [PerfectField K] :
    ∀ w ∈ ModularCurve.ssPlaces q N K,
      ModularCurve.arithFrobC q K N • w ∈ ModularCurve.ssPlaces q N K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithFrobC_smul_mem_ssPlaces.solution
