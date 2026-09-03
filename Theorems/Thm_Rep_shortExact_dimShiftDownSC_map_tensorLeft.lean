import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateDimensionShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_shortExact_dimShiftDownSC_map_tensorLeft

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.shortExact_dimShiftDownSC_map_tensorLeft {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (A : Rep.{u} k G)
    (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    ((Rep.dimShiftDownSC X).map (MonoidalCategory.tensorLeft A)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_dimShiftDownSC_map_tensorLeft.solution
