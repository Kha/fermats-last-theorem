import Mathlib
import Definitions.Def_ModularCurve_CupPairing
import Definitions.Def_ModularCurve_PeriodTransfer
import P2M.Util
import P2M.Sol.S_ModularCurve_CupPairing_pair_comp_eq_of_conjRel
attribute [-instance] CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex
attribute [-simp] CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.pair_comp_eq_of_conjRel (Γ' Γ'' : Subgroup SL(2, ℤ))
    [Γ'.FiniteIndex] [Γ''.FiniteIndex] (g : GL (Fin 2) ℝ) (e : Γ' ≃* Γ'')
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (he : ∀ γ : Γ', ModularCurve.Period.conjRel g (γ : SL(2, ℤ)) (e γ : SL(2, ℤ)))
    (x y : Additive Γ'' →+ ℚ) (hx : ModularCurve.Period.IsParabolicHom Γ'' x)
    (hy : ModularCurve.Period.IsParabolicHom Γ'' y) :
    ModularCurve.CupPairing.pair Γ' (x.comp (MonoidHom.toAdditive e.toMonoidHom))
        (y.comp (MonoidHom.toAdditive e.toMonoidHom)) =
      ModularCurve.CupPairing.pair Γ'' x y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CupPairing_pair_comp_eq_of_conjRel.solution
