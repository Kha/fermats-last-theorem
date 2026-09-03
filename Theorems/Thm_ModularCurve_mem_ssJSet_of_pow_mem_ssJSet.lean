import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_ssJSet_of_pow_mem_ssJSet

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.mem_ssJSet_of_pow_mem_ssJSet
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [DecidableEq K] [CharP K p]
    (e : ℕ) (j : K) (h : j ^ (p ^ e) ∈ ssJSet p K) : j ∈ ssJSet p K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_ssJSet_of_pow_mem_ssJSet.solution
