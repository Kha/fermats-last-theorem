import Mathlib
import Definitions.Def_ModularCurve_CupPairing
import P2M.Util
import P2M.Sol.S_ModularCurve_CupPairing_mult_mul_pair_eq_neg_finsum

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.mult_mul_pair_eq_neg_finsum (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (x y : Additive Γ →+ ℤ) (hx : ModularCurve.Period.IsParabolicHom Γ x)
    (hy : ModularCurve.Period.IsParabolicHom Γ y)
    (F : SL(2, ℤ) → ℤ) (hFT : ∀ g, F (ModularGroup.T * g) = F g) (hFneg : ∀ g, F (-g) = F g)
    (hFx : ∀ (g : SL(2, ℤ)) (γ : Γ), F (g * γ) = F g + x (Additive.ofMul γ))
    (a b : SL(2, ℤ) → ℤ) (ha : ∀ g, a (ModularGroup.S * g) = a g)
    (hb : ∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g)
    (hay : ∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + y (Additive.ofMul γ))
    (hby : ∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + y (Additive.ofMul γ))
    (Φ : SL(2, ℤ) ⧸ Γ → ℤ)
    (hΦ : ∀ g, Φ (QuotientGroup.mk g) = (F g - F (ModularGroup.S * g)) * (b g - a g)) :
    (ModularCurve.CupPairing.mult Γ : ℚ) *
        ModularCurve.CupPairing.pair Γ ((Int.castAddHom ℚ).comp x) ((Int.castAddHom ℚ).comp y) =
      -((∑ᶠ q, Φ q : ℤ) : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CupPairing_mult_mul_pair_eq_neg_finsum.solution
