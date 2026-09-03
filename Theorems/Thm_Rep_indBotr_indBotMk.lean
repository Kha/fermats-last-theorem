import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_indBotr_indBotMk

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.indBotr_indBotMk {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g : G) (a : A) :
    A.indBotr (A.indBotMk g a) = (Finsupp.single g (1 : k)) 1 • a := by p2m_exact_reverting @_root_.P2MW.S_Rep_indBotr_indBotMk.solution
