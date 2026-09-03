import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_shortExact_map_tensorRight_dimShiftDownObj

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.shortExact_map_tensorRight_dimShiftDownObj {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (B : Rep.{u} k G) (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact) :
    (X.map (MonoidalCategory.tensorRight B.dimShiftDownObj)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_map_tensorRight_dimShiftDownObj.solution
