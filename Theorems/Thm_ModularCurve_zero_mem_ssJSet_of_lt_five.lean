module

public import Mathlib
public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_zero_mem_ssJSet_of_lt_five

@[expose] public section

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.zero_mem_ssJSet_of_lt_five
    {q : ℕ} [Fact q.Prime] (hq : q < 5) {K : Type*} [Field K] [DecidableEq K] [CharP K q] :
    (0 : K) ∈ ssJSet q K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_zero_mem_ssJSet_of_lt_five.solution
