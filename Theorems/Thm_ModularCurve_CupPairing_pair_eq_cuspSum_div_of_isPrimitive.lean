import Mathlib
import Definitions.Def_ModularCurve_CupPairing
import P2M.Util
import P2M.Sol.S_ModularCurve_CupPairing_pair_eq_cuspSum_div_of_isPrimitive

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.pair_eq_cuspSum_div_of_isPrimitive (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] (φ ψ : Additive Γ →+ ℚ) (h : Γ → ℚ)
    (hh : ModularCurve.CupPairing.IsPrimitive φ ψ h) :
    ModularCurve.CupPairing.pair Γ φ ψ =
      ModularCurve.PDPairing.cuspSum Γ h / (2 * ModularCurve.CupPairing.mult Γ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CupPairing_pair_eq_cuspSum_div_of_isPrimitive.solution
