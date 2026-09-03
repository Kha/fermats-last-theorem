import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint

universe u

theorem ModularCurve.isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint
    (K : Type u) [CommRing K] (p : ℕ) [NeZero p] (c c' : Kˣ) (hc : IsUnit (1 - (c : K)))
    (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    IsUnit (ModularCurve.indepElt (ModularCurve.tateBase K p) p
      (ModularCurve.tateToricPoint K p c).1 (ModularCurve.nonToricPoint K p c' j).1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint.solution
