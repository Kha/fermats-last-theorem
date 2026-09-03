import Mathlib.FieldTheory.Perfect
import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_pow_mem_ssJSet_iff

open ModularCurve
theorem ModularCurve.pow_mem_ssJSet_iff {K : Type} [Field K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K] (a : K) :
    a ^ q ∈ ModularCurve.ssJSet q K ↔ a ∈ ModularCurve.ssJSet q K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_pow_mem_ssJSet_iff.solution
