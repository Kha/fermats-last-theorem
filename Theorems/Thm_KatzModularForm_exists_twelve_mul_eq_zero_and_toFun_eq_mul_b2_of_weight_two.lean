import Definitions.Def_ModularForm_KatzLevelOne
import P2M.Util
import P2M.Sol.S_KatzModularForm_exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single
set_option autoImplicit false
theorem KatzModularForm.exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two
    (M : ℕ) (F : KatzModularForm (ZMod M) 2) (g : PowerSeries (ZMod M))
    (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ (ZMod M) g) :
    ∃ a : ZMod M, 12 * a = 0 ∧ ∀ (A : Type) [CommRing A] [Algebra (ZMod M) A]
      (W : WeierstrassCurve A) (hW : IsUnit W.Δ),
      F.toFun W hW = algebraMap (ZMod M) A a * W.b₂ := by p2m_exact_reverting @_root_.P2MW.S_KatzModularForm_exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two.solution
