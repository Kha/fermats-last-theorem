import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_dimShiftUp_shortExact

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.dimShiftUp_shortExact {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) :
    (A.dimShiftUp).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_dimShiftUp_shortExact.solution
