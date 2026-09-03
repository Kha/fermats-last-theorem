import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_normFreeEnd_normFreeEnd_eq_card_nsmul

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~sum_diamondOneBar_normFreeEnd_eq_zero"

theorem ModularCurve.normFreeEnd_normFreeEnd_eq_card_nsmul
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M)
    (hIn : ModularCurve.HeckeDiamondInputsAll M) (x : JOne M) :
    normFreeEnd M (normFreeRepsAt M p) (normFreeEnd M (normFreeRepsAt M p) x) =
      (normFreeRepsAt M p).card • normFreeEnd M (normFreeRepsAt M p) x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_normFreeEnd_normFreeEnd_eq_card_nsmul.solution
