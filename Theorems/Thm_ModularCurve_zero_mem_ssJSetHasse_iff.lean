import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Util
import P2M.Sol.S_ModularCurve_zero_mem_ssJSetHasse_iff

open ModularCurve
theorem ModularCurve.zero_mem_ssJSetHasse_iff (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] : (0 : K) ∈ ssJSetHasse q K ↔ q % 3 = 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_zero_mem_ssJSetHasse_iff.solution
