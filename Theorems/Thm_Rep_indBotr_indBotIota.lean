import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_indBotr_indBotIota

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.indBotr_indBotIota {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (a : A) :
    A.indBotr ((Rep.indBotι A).hom a) = a := by p2m_exact_reverting @_root_.P2MW.S_Rep_indBotr_indBotIota.solution
