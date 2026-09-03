import Mathlib
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul
attribute [-instance] WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk
attribute [-simp] WeierstrassCurve.vcInvEmbedding_apply

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul
    {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] {x₀ y₀ : K}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    ∃ (x₁ y₁ : K) (hQ₁ : (W.veluQuotient2 x₀ y₀).toAffine.Equation x₁ y₁)
      (hgy₁ : (W.veluQuotient2 x₀ y₀).veluGy x₁ y₁ = 0)
      (hΔ₁ : ((W.veluQuotient2 x₀ y₀).veluQuotient2 x₁ y₁).Δ ≠ 0)
      (C : VariableChange K) (hC : C • W = (W.veluQuotient2 x₀ y₀).veluQuotient2 x₁ y₁),
      (∀ x y : K, W.toAffine.Equation x y → W.veluGy x y = 0 → x ≠ x₀ →
          W.velu2X x₀ y₀ x = x₁ ∧ W.velu2Y x₀ y₀ x y = y₁) ∧
      ∀ P : W.toAffine.Point,
        Point.equivOfVariableChangeEq hC
            (veluPointMap2 h2 hQ₁ hgy₁ hΔ₁ (veluPointMap2 h2 hQ hgy hΔ P))
          = (2 : ℤ) • P := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul.solution
