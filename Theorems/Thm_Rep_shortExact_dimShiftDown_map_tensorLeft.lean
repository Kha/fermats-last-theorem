import Mathlib
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_shortExact_dimShiftDown_map_tensorLeft

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.shortExact_dimShiftDown_map_tensorLeft {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) :
    (B.dimShiftDown.map (MonoidalCategory.tensorLeft A)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_dimShiftDown_map_tensorLeft.solution
