import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateDimensionShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_dimShiftDownSC_shortExact

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.dimShiftDownSC_shortExact {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep.{u} k G)}
    (hX : X.ShortExact) : (Rep.dimShiftDownSC X).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_dimShiftDownSC_shortExact.solution
