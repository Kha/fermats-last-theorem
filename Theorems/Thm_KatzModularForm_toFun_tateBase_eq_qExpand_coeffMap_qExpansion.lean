import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_KatzModularForm_toFun_tateBase_eq_qExpand_coeffMap_qExpansion

universe u

theorem KatzModularForm.toFun_tateBase_eq_qExpand_coeffMap_qExpansion
    {R₀ : Type u} [CommRing R₀] {k : ℤ} (g : KatzModularForm R₀ k)
    (R : Type u) [CommRing R] [Algebra R₀ R] (p : ℕ) [NeZero p] :
    g.toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p)
      = ModularCurve.qExpand R p (ModularCurve.coeffMap (algebraMap R₀ R) g.qExpansion) := by p2m_exact_reverting @_root_.P2MW.S_KatzModularForm_toFun_tateBase_eq_qExpand_coeffMap_qExpansion.solution
