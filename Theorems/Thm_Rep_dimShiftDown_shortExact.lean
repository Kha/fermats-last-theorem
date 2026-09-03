import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_dimShiftDown_shortExact

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.dimShiftDown_shortExact {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) :
    (A.dimShiftDown).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_dimShiftDown_shortExact.solution
