import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.jqNModC_pow_eq_jqNModC_mul_of_charP
    (K : Type) [CommRing K] (q : ℕ) [Fact q.Prime] [CharP K q] (n : ℕ) [NeZero n] [NeZero (q * n)] :
    (jqNModC K n) ^ q = jqNModC K (q * n) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP.solution
