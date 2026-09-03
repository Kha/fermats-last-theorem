import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one

open ModularCurve

universe u in

theorem ModularCurve.qTwist_nonToricPoint_of_pow_eq_one
    (K : Type u) [CommRing K] (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : ζ ^ M = 1) (c : Kˣ)
    (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    (qTwist ζ (nonToricPoint K M c j).1, qTwist ζ (nonToricPoint K M c j).2) =
      nonToricPoint K M (c * ζ ^ j) j := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one.solution
