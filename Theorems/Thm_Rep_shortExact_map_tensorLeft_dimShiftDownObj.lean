import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_shortExact_map_tensorLeft_dimShiftDownObj

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.shortExact_map_tensorLeft_dimShiftDownObj {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (A : Rep.{u} k G) (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    (X.map (MonoidalCategory.tensorLeft A.dimShiftDownObj)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_map_tensorLeft_dimShiftDownObj.solution
