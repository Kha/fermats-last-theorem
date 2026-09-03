import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_heq_fullKernelHom_vcInvFun
attribute [-simp] WeierstrassCurve.vcInvEmbedding_apply

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem WeierstrassCurve.heq_fullKernelHom_vcInvFun
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (C : VariableChange F)
    (Q : W.toAffine.Point) {N : ℕ} (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (φ' : (C • W).toAffine.Point →+
      ((C • W).fullKernelQuotient (Point.vcInvFun C W.toAffine Q) N).toAffine.Point)
    (hφ'ker : φ'.ker = AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q))
    (hφ' : ∀ P : (C • W).toAffine.Point, P ∉ AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q) →
      (φ' P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Point.vcInvFun C W.toAffine Q).coordsOrZero.1 -
              (k • Point.vcInvFun C W.toAffine Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Point.vcInvFun C W.toAffine Q).coordsOrZero.2 -
              (k • Point.vcInvFun C W.toAffine Q).coordsOrZero.2)))
    (P : W.toAffine.Point) :
    HEq (φ' (Point.vcInvFun C W.toAffine P))
      (Point.vcInvFun C (W.fullKernelQuotient Q N).toAffine (φ P)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_heq_fullKernelHom_vcInvFun.solution
