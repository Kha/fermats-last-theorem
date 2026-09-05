module

public import Mathlib
public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_ssJSet_finite

@[expose] public section

open ModularCurve
namespace ModularCurve
theorem ssJSet_finite (q : ℕ) [Fact q.Prime]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    (ssJSet q K).Finite := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ssJSet_finite.solution
end ModularCurve
