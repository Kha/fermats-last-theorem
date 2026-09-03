import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_card_normFreeRepsAt_eq_sub_one

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.card_normFreeRepsAt_eq_sub_one
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M) :
    (normFreeRepsAt M p).card = p - 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_card_normFreeRepsAt_eq_sub_one.solution
