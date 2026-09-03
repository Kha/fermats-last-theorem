import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.vcInvEmbedding_apply

theorem WeierstrassCurve.exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0) (W : WeierstrassCurve K) [W.IsElliptic] {x₀ y₀ : K} (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) : ∃ π : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point, ⇑π = WeierstrassCurve.veluPointMap2 h2 hQ hgy hΔ ∧ π ∈ WeierstrassCurve.rationalHomSet K W (W.veluQuotient2 x₀ y₀) ∧ (∃ π' ∈ WeierstrassCurve.rationalHomSet K (W.veluQuotient2 x₀ y₀) W, π'.comp π = 2 • AddMonoidHom.id _ ∧ π.comp π' = 2 • AddMonoidHom.id _) ∧ ∀ (W₃ : WeierstrassCurve K) (_ : W₃.IsElliptic) (α : W.toAffine.Point →+ W₃.toAffine.Point), α ∈ WeierstrassCurve.rationalHomSet K W W₃ → (∀ T, π T = 0 → α T = 0) → ∃ β ∈ WeierstrassCurve.rationalHomSet K (W.veluQuotient2 x₀ y₀) W₃, α = β.comp π := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul.solution
