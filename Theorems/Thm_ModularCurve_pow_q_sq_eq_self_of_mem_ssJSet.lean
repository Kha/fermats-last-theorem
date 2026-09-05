module

public import Mathlib
public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet

@[expose] public section

open ModularCurve
theorem ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] {a : K} (ha : a ∈ ModularCurve.ssJSet q K) : a ^ (q ^ 2) = a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet.solution
