module

public import Mathlib
public import Definitions.Def_ModularCurve_SupersingularModuli
public import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Sol.S_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
import P2M.Util

namespace P2MW.S_ModularCurve_ssJSet_eq_ssJSetHasse

set_option autoImplicit false

open ModularCurve

theorem solution (q : ℕ) [Fact q.Prime] (hq : q ≠ 2)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ssJSet q K = ssJSetHasse q K := by
  ext j
  simp only [ModularCurve.ssJSet, ModularCurve.ssJSetHasse, Set.mem_setOf_eq]
  constructor
  · intro h W _ hj
    exact (W.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero q hq).mp (h W hj)
  · intro h W _ hj
    exact (W.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero q hq).mpr (h W hj)
end S_ModularCurve_ssJSet_eq_ssJSetHasse
end P2MW

public section
open ModularCurve
theorem ModularCurve.ssJSet_eq_ssJSetHasse (q : ℕ) [Fact q.Prime] (hq : q ≠ 2)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ssJSet q K = ssJSetHasse q K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ssJSet_eq_ssJSetHasse.solution
end
