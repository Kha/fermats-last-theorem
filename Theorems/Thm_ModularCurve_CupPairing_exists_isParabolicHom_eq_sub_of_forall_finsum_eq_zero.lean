import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (f : SL(2, ℤ) ⧸ Γ → ℤ)
    (hf : ∀ e : SL(2, ℤ) ⧸ Γ → ℤ, (∀ q, e (ModularGroup.T • q) = e q) →
      ∑ᶠ q, f q * (e q - e (ModularGroup.S • q)) = 0) :
    ∃ φ : Additive Γ →+ ℤ, ModularCurve.Period.IsParabolicHom Γ φ ∧
      ∃ a b : SL(2, ℤ) → ℤ, (∀ g, a (ModularGroup.S * g) = a g) ∧
        (∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g) ∧
        (∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + φ (Additive.ofMul γ)) ∧
        (∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + φ (Additive.ofMul γ)) ∧
        ∀ g, f (QuotientGroup.mk g) = b g - a g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.solution
