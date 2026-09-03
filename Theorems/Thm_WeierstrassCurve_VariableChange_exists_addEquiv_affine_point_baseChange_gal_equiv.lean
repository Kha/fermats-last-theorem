import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_VariableChange_exists_addEquiv_affine_point_baseChange_gal_equiv
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem WeierstrassCurve.VariableChange.exists_addEquiv_affine_point_baseChange_gal_equiv
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K)
    (C : WeierstrassCurve.VariableChange K) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ e : ((C • W)⁄(AlgebraicClosure K)).Point ≃+ (W⁄(AlgebraicClosure K)).Point,
      ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) P,
        e (σ • P) = σ • (e P) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_VariableChange_exists_addEquiv_affine_point_baseChange_gal_equiv.solution
