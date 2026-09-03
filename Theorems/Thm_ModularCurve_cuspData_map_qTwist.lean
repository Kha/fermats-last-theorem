import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_cuspData_map_qTwist

universe u

theorem ModularCurve.cuspData_map_qTwist {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    (ζ : Rˣ) (hζ : ζ ^ p = 1) (v w : Fin 2 → ZMod p) :
    (ModularCurve.cuspData R p ζ v w).map (ModularCurve.qTwist ζ)
      = ModularCurve.cuspData R p ζ (ModularCurve.cuspShift p v) (ModularCurve.cuspShift p w) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_cuspData_map_qTwist.solution
