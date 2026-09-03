import Mathlib
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange

set_option autoImplicit false

universe u

theorem ModularCurve.kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange
    (T : Type u) [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (ℓ d n : ℕ) (h : Polynomial T) (x : T)
    (hx : h ∣ ModularCurve.inLineMulPoly W ℓ n x) :
    ModularCurve.kernelVariableChangeDeg C d h ∣
      ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange.solution
