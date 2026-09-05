module

public import Mathlib
public import Definitions.Def_ModularCurve_SupersingularModuli
public import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Util
import P2M.Sol.S_ModularCurve_ssJSet_eq_ssJSetHasse

@[expose] public section

open ModularCurve
theorem ModularCurve.ssJSet_eq_ssJSetHasse (q : ℕ) [Fact q.Prime] (hq : q ≠ 2)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ssJSet q K = ssJSetHasse q K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ssJSet_eq_ssJSetHasse.solution
