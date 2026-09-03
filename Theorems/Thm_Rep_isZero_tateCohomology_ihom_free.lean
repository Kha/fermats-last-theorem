import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationHomDefect
import P2M.Util
import P2M.Sol.S_Rep_isZero_tateCohomology_ihom_free
set_option autoImplicit false
open CategoryTheory

theorem Rep.isZero_tateCohomology_ihom_free {G : Type} [Group G] [Fintype G] (B C : Rep ℤ G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (((ihom (Rep.free ℤ G B)).obj C).tateCohomology q) := by p2m_exact_reverting @_root_.P2MW.S_Rep_isZero_tateCohomology_ihom_free.solution
