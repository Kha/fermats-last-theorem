import Mathlib
import Definitions.Def_WeierstrassCurve_LevelThreeModulus
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_of_levelThreeModulus_eq

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_variableChange_of_levelThreeModulus_eq
    {F : Type*} [Field F] [DecidableEq F] (h3 : (3 : F) ≠ 0) (E E' : WeierstrassCurve F)
    {x₁ y₁ x₂ y₂ : F} (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (3 : ℤ) • (Point.some x₁ y₁ h₁) = 0) (hP₂ : (3 : ℤ) • (Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂)
    {x₁' y₁' x₂' y₂' : F} (h₁' : E'.toAffine.Nonsingular x₁' y₁')
    (h₂' : E'.toAffine.Nonsingular x₂' y₂')
    (hP₁' : (3 : ℤ) • (Point.some x₁' y₁' h₁') = 0) (hP₂' : (3 : ℤ) • (Point.some x₂' y₂' h₂') = 0)
    (hx' : x₁' ≠ x₂')
    (hτ : E.levelThreeModulus x₁ y₁ x₂ = E'.levelThreeModulus x₁' y₁' x₂') :
    E.levelThreeAbscissa x₁ y₁ x₂ = E'.levelThreeAbscissa x₁' y₁' x₂' ∧
    (E'.levelThreeOrdinate x₁' y₁' x₂' y₂' = E.levelThreeOrdinate x₁ y₁ x₂ y₂ ∨
      E'.levelThreeOrdinate x₁' y₁' x₂' y₂' = -E.levelThreeOrdinate x₁ y₁ x₂ y₂
        - (E.levelThreeModulus x₁ y₁ x₂ + 1) * E.levelThreeAbscissa x₁ y₁ x₂) ∧
    ∃ γ : VariableChange F, ∃ hγ : γ • E = E',
      Point.equivOfVariableChangeEq hγ (.some x₁' y₁' h₁') = .some x₁ y₁ h₁ ∧
      (Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂ ∨
        Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = -.some x₂ y₂ h₂) ∧
      (E.levelThreeOrdinate x₁ y₁ x₂ y₂ = E'.levelThreeOrdinate x₁' y₁' x₂' y₂' →
        Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_of_levelThreeModulus_eq.solution
