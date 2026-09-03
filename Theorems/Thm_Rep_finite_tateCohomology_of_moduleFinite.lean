import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_finite_tateCohomology_of_moduleFinite
attribute [-simp] Rep.coe_tateδneg2_apply

set_option autoImplicit false
open CategoryTheory Rep
theorem Rep.finite_tateCohomology_of_moduleFinite {G : Type} [Group G] [Fintype G]
    (L : Rep ℤ G) [Module.Finite ℤ L] (n : ℤ) :
    Finite (L.tateCohomology n) := by p2m_exact_reverting @_root_.P2MW.S_Rep_finite_tateCohomology_of_moduleFinite.solution
