import Mathlib
import Definitions.Def_LaurentSeries_XAdic
import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_tateCurve_pointY_C_eq_tateToricPoint_snd

open scoped LaurentSeries.XAdic

theorem ModularCurve.tateCurve_pointY_C_eq_tateToricPoint_snd (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (hc : (c : F) ≠ 1) :
    TateCurve.pointY ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C (c : F))
      = (ModularCurve.tateToricPoint F p c).2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_tateCurve_pointY_C_eq_tateToricPoint_snd.solution
