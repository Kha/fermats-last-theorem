import Mathlib
import Definitions.Def_ModularCurve_PDPairing
import P2M.Util
import P2M.Sol.S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.cuspSum_eq_sum_finsum_of_le (Γ' Γ : Subgroup SL(2, ℤ))
    [Γ'.FiniteIndex] [Γ.FiniteIndex] (hle : Γ' ≤ Γ) (F : SL(2, ℤ) → ℚ)
    (hF : ∀ p ∈ Γ', ∀ δ ∈ Γ', (p : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
      F (δ * p * δ⁻¹) = F p) :
    ModularCurve.PDPairing.cuspSum Γ' (fun γ => F γ) =
      ∑ Q : ModularCurve.PDPairing.Cusp Γ,
        ∑ᶠ O : MulAction.orbitRel.Quotient
            (Subgroup.zpowers (ModularCurve.PDPairing.cuspGen Γ Q)) (Γ ⧸ Γ'.subgroupOf Γ),
          F ((O.out.out⁻¹ * ModularCurve.PDPairing.cuspGen Γ Q ^
              Function.minimalPeriod (ModularCurve.PDPairing.cuspGen Γ Q • ·) O.out *
              O.out.out : Γ) : SL(2, ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le.solution
