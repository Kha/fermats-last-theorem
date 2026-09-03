import Definitions.Def_ModularForm_KatzLevelOne
import P2M.Util
import P2M.Sol.S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six
set_option autoImplicit false
theorem KatzModularForm.toFun_eq_zero_of_weight_two_of_isUnit_six
    (R : Type) [CommRing R] (h6 : IsUnit (6 : R)) (F : KatzModularForm R 2)
    (g : PowerSeries R) (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ R g)
    (A : Type) [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    F.toFun W hW = 0 := by p2m_exact_reverting @_root_.P2MW.S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six.solution
