import Definitions.Def_ModularForm_KatzLevelOne
import P2M.Util
import P2M.Sol.S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_three_pow
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single
set_option autoImplicit false
theorem KatzModularForm.exists_toFun_eq_mul_b2_of_weight_two_zmod_three_pow
    (e : ℕ) (F : KatzModularForm (ZMod (3^e)) 2) (g : PowerSeries (ZMod (3^e)))
    (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ (ZMod (3^e)) g) :
    ∃ a : ZMod (3^e), 3 * a = 0 ∧ ∀ (A : Type) [CommRing A] [Algebra (ZMod (3^e)) A]
      (W : WeierstrassCurve A) (hW : IsUnit W.Δ),
      F.toFun W hW = algebraMap (ZMod (3^e)) A a * W.b₂ := by p2m_exact_reverting @_root_.P2MW.S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_three_pow.solution
