import Mathlib
import Definitions.Def_WeierstrassCurve_LevelThreeModulus
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_eq_deuringCurve_of_three_smul_eq_zero

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_variableChange_eq_deuringCurve_of_three_smul_eq_zero
    {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) {x₁ y₁ x₂ y₂ : F}
    (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (3 : ℤ) • (Point.some x₁ y₁ h₁) = 0) (hx : x₁ ≠ x₂) :
    E.deuringA₃ x₁ y₁ ≠ 0 ∧ E.levelThreeAbscissa x₁ y₁ x₂ ≠ 0 ∧
    ∃ κ : VariableChange F,
      ((κ.u : F) = E.deuringA₃ x₁ y₁ / (x₂ - x₁) ∧ κ.r = x₁ ∧ κ.s = E.tangentSlope x₁ y₁ ∧ κ.t = y₁) ∧
    ∃ hκ : κ • E = deuringCurve (E.levelThreeModulus x₁ y₁ x₂) (E.levelThreeAbscissa x₁ y₁ x₂),
    ∃ h₀ : (deuringCurve (E.levelThreeModulus x₁ y₁ x₂) (E.levelThreeAbscissa x₁ y₁ x₂)).toAffine.Nonsingular 0 0,
    ∃ h₂' : (deuringCurve (E.levelThreeModulus x₁ y₁ x₂) (E.levelThreeAbscissa x₁ y₁ x₂)).toAffine.Nonsingular
        (E.levelThreeAbscissa x₁ y₁ x₂) (E.levelThreeOrdinate x₁ y₁ x₂ y₂),
      Point.equivOfVariableChangeEq hκ (.some 0 0 h₀) = .some x₁ y₁ h₁ ∧
      Point.equivOfVariableChangeEq hκ (.some _ _ h₂') = .some x₂ y₂ h₂ ∧
      ((3 : ℤ) • (Point.some x₂ y₂ h₂) = 0 →
        3 * E.levelThreeAbscissa x₁ y₁ x₂ + E.levelThreeModulus x₁ y₁ x₂ ^ 2
          + 3 * E.levelThreeModulus x₁ y₁ x₂ + 3 = 0 ∧
        2 * E.levelThreeOrdinate x₁ y₁ x₂ y₂ + E.levelThreeModulus x₁ y₁ x₂ * E.levelThreeAbscissa x₁ y₁ x₂
          + E.levelThreeAbscissa x₁ y₁ x₂ ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_eq_deuringCurve_of_three_smul_eq_zero.solution
