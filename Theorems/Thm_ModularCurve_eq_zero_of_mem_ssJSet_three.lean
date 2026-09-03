import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_eq_zero_of_mem_ssJSet_three

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.eq_zero_of_mem_ssJSet_three
    {k : Type*} [Field k] [CharP k 3] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet 3 k) (ha2 : a ^ (3 ^ 2) = a) : a = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eq_zero_of_mem_ssJSet_three.solution
