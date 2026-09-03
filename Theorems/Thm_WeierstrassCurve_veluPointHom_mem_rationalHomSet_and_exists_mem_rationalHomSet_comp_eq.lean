import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
attribute [-simp] WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero

theorem WeierstrassCurve.veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (φ : W.toAffine.Point →+ (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (W.veluX (W.oddOrderSummingSet Q n) x)
          (W.veluY (W.oddOrderSummingSet Q n) x y) h') :
    φ ∈ WeierstrassCurve.rationalHomSet F W (W.veluQuotient (W.oddOrderSummingSet Q n)) ∧
      ∀ (W₃ : WeierstrassCurve F) [W₃.IsElliptic] (α : W.toAffine.Point →+ W₃.toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet F W W₃ → α Q = 0 →
          ∃ β ∈ WeierstrassCurve.rationalHomSet F (W.veluQuotient (W.oddOrderSummingSet Q n)) W₃,
            α = β.comp φ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq.solution
