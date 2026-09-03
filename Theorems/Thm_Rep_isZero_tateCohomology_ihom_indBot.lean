import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_isZero_tateCohomology_ihom_indBot

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.isZero_tateCohomology_ihom_indBot {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A W : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (((ihom A.indBot).obj W).tateCohomology q) := by p2m_exact_reverting @_root_.P2MW.S_Rep_isZero_tateCohomology_ihom_indBot.solution
