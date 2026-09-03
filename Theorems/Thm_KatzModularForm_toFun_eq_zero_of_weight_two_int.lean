import Definitions.Def_ModularForm_KatzLevelOne
import P2M.Util
import P2M.Sol.S_KatzModularForm_toFun_eq_zero_of_weight_two_int
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single
set_option autoImplicit false
theorem KatzModularForm.toFun_eq_zero_of_weight_two_int
    (F : KatzModularForm (ZMod 0) 2) (g : PowerSeries (ZMod 0))
    (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ (ZMod 0) g)
    (A : Type) [CommRing A] [Algebra (ZMod 0) A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    F.toFun W hW = 0 := by p2m_exact_reverting @_root_.P2MW.S_KatzModularForm_toFun_eq_zero_of_weight_two_int.solution
