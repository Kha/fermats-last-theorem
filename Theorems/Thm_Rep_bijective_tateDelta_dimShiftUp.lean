import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_bijective_tateDelta_dimShiftUp

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.bijective_tateDelta_dimShiftUp {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (hA : A.dimShiftUp.ShortExact) (n : ℤ) :
    Function.Bijective (Rep.tateδ hA n).hom := by p2m_exact_reverting @_root_.P2MW.S_Rep_bijective_tateDelta_dimShiftUp.solution
