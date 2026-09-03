import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_WeierstrassCurve_LegendreModulus
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_of_legendreLambda_eq

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_variableChange_of_legendreLambda_eq {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0) (E E' : WeierstrassCurve F) {x₁ y₁ x₂ y₂ : F} (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂) (hP₁ : (2 : ℤ) • (Point.some x₁ y₁ h₁) = 0) (hP₂ : (2 : ℤ) • (Point.some x₂ y₂ h₂) = 0) (hx : x₁ ≠ x₂) {x₁' y₁' x₂' y₂' : F} (h₁' : E'.toAffine.Nonsingular x₁' y₁') (h₂' : E'.toAffine.Nonsingular x₂' y₂') (hP₁' : (2 : ℤ) • (Point.some x₁' y₁' h₁') = 0) (hP₂' : (2 : ℤ) • (Point.some x₂' y₂' h₂') = 0) (hx' : x₁' ≠ x₂') {u : F} (hu : u ^ 2 * (x₂' - x₁') = x₂ - x₁) (hl : E.legendreLambda x₁ x₂ = E'.legendreLambda x₁' x₂') :
    ∃ γ : VariableChange F, ∃ hγ : γ • E = E',
      Point.equivOfVariableChangeEq hγ (.some x₁' y₁' h₁') = .some x₁ y₁ h₁ ∧
      Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_of_legendreLambda_eq.solution
