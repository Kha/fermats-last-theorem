import Definitions.Def_ModularForm_KatzLevelOne
import P2M.Util
import P2M.Sol.S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two
set_option autoImplicit false
theorem KatzModularForm.exists_toFun_eq_mul_b2_of_weight_two_zmod_two
    (F : KatzModularForm (ZMod 2) 2) (g : PowerSeries (ZMod 2))
    (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ (ZMod 2) g) :
    ∃ a : ZMod 2, 4 * a = 0 ∧ ∀ (A : Type) [CommRing A] [Algebra (ZMod 2) A]
      (W : WeierstrassCurve A) (hW : IsUnit W.Δ),
      F.toFun W hW = algebraMap (ZMod 2) A a * W.b₂ := by p2m_exact_reverting @_root_.P2MW.S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two.solution
