import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_eq_of_veluQuotient2_j_eq_of_not_isIntegral_j
attribute [-instance] WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4
attribute [-simp] WeierstrassCurve.veluX_empty

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.eq_of_veluQuotient2_j_eq_of_not_isIntegral_j
    {F : Type*} [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (hj : ¬ _root_.IsIntegral ℤ W.j)
    {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (hg₁ : W.veluGy x₁ y₁ = 0)
    (h₂ : W.toAffine.Equation x₂ y₂) (hg₂ : W.veluGy x₂ y₂ = 0)
    (hΔ₁ : (W.veluQuotient2 x₁ y₁).Δ ≠ 0) (hΔ₂ : (W.veluQuotient2 x₂ y₂).Δ ≠ 0)
    (hjeq : @WeierstrassCurve.j F _ (W.veluQuotient2 x₁ y₁) ⟨isUnit_iff_ne_zero.mpr hΔ₁⟩ =
      @WeierstrassCurve.j F _ (W.veluQuotient2 x₂ y₂) ⟨isUnit_iff_ne_zero.mpr hΔ₂⟩) :
    x₁ = x₂ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_eq_of_veluQuotient2_j_eq_of_not_isIntegral_j.solution
