import Mathlib
import Definitions.Def_ModularCurve_CupPairing
import P2M.Util
import P2M.Sol.S_ModularCurve_CupPairing_exists_isPrimitive

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.exists_isPrimitive (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (φ ψ : Additive Γ →+ ℚ) :
    ∃ h : Γ → ℚ, ModularCurve.CupPairing.IsPrimitive φ ψ h := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CupPairing_exists_isPrimitive.solution
