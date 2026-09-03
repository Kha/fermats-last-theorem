import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_sum_diamondOneBar_normFreeEnd_eq_zero

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.sum_diamondOneBar_normFreeEnd_eq_zero
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M)
    (hIn : ModularCurve.HeckeDiamondInputsAll M) (x : JOne M) :
    (∑ d ∈ normFreeRepsAt M p, diamondOneBar M d (normFreeEnd M (normFreeRepsAt M p) x) = 0) ∧
    (normFreeEnd M (normFreeRepsAt M p) (∑ d ∈ normFreeRepsAt M p, diamondOneBar M d x) = 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_diamondOneBar_normFreeEnd_eq_zero.solution
