import Mathlib
import Definitions.Def_ModularCurve_PDPairing
import Definitions.Def_ModularCurve_PeriodTransfer
import P2M.Util
import P2M.Sol.S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.cuspSum_comp_eq_of_conjRel (Γ' Γ'' : Subgroup SL(2, ℤ))
    [Γ'.FiniteIndex] [Γ''.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ')
    (g : GL (Fin 2) ℝ) (e : Γ' ≃* Γ'') (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (he : ∀ γ : Γ', ModularCurve.Period.conjRel g (γ : SL(2, ℤ)) (e γ : SL(2, ℤ)))
    (F : Γ'' → ℚ)
    (hF : ∀ p δ : Γ'', ((p : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
      F (δ * p * δ⁻¹) = F p) :
    ModularCurve.PDPairing.cuspSum Γ' (fun γ => F (e γ)) = ModularCurve.PDPairing.cuspSum Γ'' F := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel.solution
