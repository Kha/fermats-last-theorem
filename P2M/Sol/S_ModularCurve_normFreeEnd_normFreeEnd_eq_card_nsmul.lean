import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

import Theorems.Thm_ModularCurve_sum_diamondOneBar_normFreeEnd_eq_zero
import P2M.Util
namespace P2MW.S_ModularCurve_normFreeEnd_normFreeEnd_eq_card_nsmul

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M)
    (hIn : ModularCurve.HeckeDiamondInputsAll M) (x : JOne M) :
    normFreeEnd M (normFreeRepsAt M p) (normFreeEnd M (normFreeRepsAt M p) x) =
      (normFreeRepsAt M p).card • normFreeEnd M (normFreeRepsAt M p) x := by

  rw [normFreeEnd_apply M (normFreeRepsAt M p) (normFreeEnd M (normFreeRepsAt M p) x),
    (ModularCurve.sum_diamondOneBar_normFreeEnd_eq_zero M p hpM hIn x).1, sub_zero]
