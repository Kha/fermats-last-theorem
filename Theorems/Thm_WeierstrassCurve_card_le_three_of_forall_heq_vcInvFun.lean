import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.card_le_three_of_forall_heq_vcInvFun
    {K : Type*} [Field K] [DecidableEq K] (E : WeierstrassCurve K)
    (β : WeierstrassCurve.VariableChange K) (hβ : β • E = E) (h1 : β ≠ 1)
    (hneg : β ≠ ⟨-1, 0, -E.a₁, -E.a₃⟩)
    (F : Finset E.toAffine.Point) (hF : ∀ P ∈ F, HEq (Point.vcInvFun β E.toAffine P) P) :
    F.card ≤ 3 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun.solution
