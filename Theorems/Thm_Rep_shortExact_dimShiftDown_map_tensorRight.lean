import Mathlib
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_shortExact_dimShiftDown_map_tensorRight

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.shortExact_dimShiftDown_map_tensorRight {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) :
    (A.dimShiftDown.map (MonoidalCategory.tensorRight B)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_dimShiftDown_map_tensorRight.solution
