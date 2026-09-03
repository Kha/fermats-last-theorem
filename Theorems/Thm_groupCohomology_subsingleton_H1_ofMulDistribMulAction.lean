import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_subsingleton_H1_ofMulDistribMulAction

set_option autoImplicit false
open groupCohomology
theorem groupCohomology.subsingleton_H1_ofMulDistribMulAction
    {G V : Type} [Group G] [CommGroup V] [MulDistribMulAction G V]
    (h : ∀ f : G → V, IsMulCocycle₁ f → IsMulCoboundary₁ f) :
    Subsingleton (H1 (Rep.ofMulDistribMulAction G V)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_subsingleton_H1_ofMulDistribMulAction.solution
