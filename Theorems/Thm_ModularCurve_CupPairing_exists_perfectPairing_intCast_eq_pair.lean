import Mathlib
import Definitions.Def_ModularCurve_CupPairing
import P2M.Util
import P2M.Sol.S_ModularCurve_CupPairing_exists_perfectPairing_intCast_eq_pair

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.exists_perfectPairing_intCast_eq_pair (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] :
    ∃ IP : ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ℤ,
      Function.Bijective IP ∧ Function.Bijective IP.flip ∧
      ∀ x y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ,
        (IP x y : ℚ) = ModularCurve.CupPairing.pair Γ
          ((Int.castAddHom ℚ).comp (x : Additive Γ →+ ℤ))
          ((Int.castAddHom ℚ).comp (y : Additive Γ →+ ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CupPairing_exists_perfectPairing_intCast_eq_pair.solution
