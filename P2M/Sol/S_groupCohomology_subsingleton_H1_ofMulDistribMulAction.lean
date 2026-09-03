import Mathlib
import P2M.Util
namespace P2MW.S_groupCohomology_subsingleton_H1_ofMulDistribMulAction

set_option autoImplicit false
open groupCohomology

set_option maxHeartbeats 1600000 in
theorem solution
    {G V : Type} [Group G] [CommGroup V] [MulDistribMulAction G V]
    (h : ∀ f : G → V, IsMulCocycle₁ f → IsMulCoboundary₁ f) :
    Subsingleton (H1 (Rep.ofMulDistribMulAction G V)) := by

  refine subsingleton_of_forall_eq 0 fun a => H1_induction_on a fun x => (H1π_eq_zero_iff x).2 ?_

  refine (coboundariesOfIsMulCoboundary₁ ?_).2
  exact h _ (isMulCocycle₁_of_mem_cocycles₁ _ x.2)
