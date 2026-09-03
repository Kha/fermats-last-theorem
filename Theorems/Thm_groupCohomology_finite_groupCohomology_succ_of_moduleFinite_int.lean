import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_groupCohomology_finite_groupCohomology_succ_of_moduleFinite_int
attribute [-simp] Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology
theorem groupCohomology.finite_groupCohomology_succ_of_moduleFinite_int {G : Type} [Group G] [Finite G]
    (L : Rep ℤ G) [Module.Finite ℤ L] (n : ℕ) :
    Finite (groupCohomology L (n + 1)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finite_groupCohomology_succ_of_moduleFinite_int.solution
