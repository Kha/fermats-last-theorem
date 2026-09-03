import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_nonempty_tate_addEquiv_elementwise

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.nonempty_tate_addEquiv_elementwise
    {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (D N : M →* M)
    (hD : ∀ x, D x = g • x / x) (hN : ∀ x, N x = ∏ h : G, h • x) :
    Nonempty ((Rep.ofMulDistribMulAction G M).tateH0 ≃+ Additive (D.ker ⧸ N.range.subgroupOf D.ker)) ∧
    Nonempty ((Rep.ofMulDistribMulAction G M).tateHneg1 ≃+ Additive (N.ker ⧸ D.range.subgroupOf N.ker)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_tate_addEquiv_elementwise.solution
