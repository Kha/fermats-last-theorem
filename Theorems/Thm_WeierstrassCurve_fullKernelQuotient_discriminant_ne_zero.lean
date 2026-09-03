import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
attribute [-simp] WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluPointMap2_zero

theorem WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero
    {F : Type*} [Field F] [DecidableEq F] :
    ∀ (N : ℕ) (W : WeierstrassCurve F) [W.IsElliptic], (N : F) ≠ 0 →
      ∀ (Q : W.toAffine.Point), addOrderOf Q = N → (W.fullKernelQuotient Q N).Δ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero.solution
