import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_isZero_tateCohomology_ihom_indBot_trivial

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.isZero_tateCohomology_ihom_indBot_trivial {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (M : ModuleCat.{u} k) (W : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (((ihom (Rep.trivial k G M).indBot).obj W).tateCohomology q) := by p2m_exact_reverting @_root_.P2MW.S_Rep_isZero_tateCohomology_ihom_indBot_trivial.solution
