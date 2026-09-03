import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_neg_mem_rationalHomSet
import P2M.Util
namespace P2MW.S_WeierstrassCurve_mem_rationalEndSubring_iff_mem_rationalHomSet

set_option autoImplicit false

theorem solution
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (α : AddMonoid.End (W.baseChange k).toAffine.Point) :
    α ∈ WeierstrassCurve.rationalEndSubring k W ↔
      (α : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
        WeierstrassCurve.rationalHomSet k W W := by
  constructor
  · intro h
    unfold WeierstrassCurve.rationalEndSubring at h
    induction h using Subring.closure_induction with
    | mem x hx => exact hx
    | zero => exact WeierstrassCurve.zero_mem_rationalHomSet k W W
    | one => exact WeierstrassCurve.id_mem_rationalHomSet k W
    | add x y _ _ hx hy => exact WeierstrassCurve.add_mem_rationalHomSet k W W hx hy
    | neg x _ hx => exact WeierstrassCurve.neg_mem_rationalHomSet k W W hx
    | mul x y _ _ hx hy => exact WeierstrassCurve.comp_mem_rationalHomSet k W W W hy hx
  · intro h
    exact Subring.subset_closure h
