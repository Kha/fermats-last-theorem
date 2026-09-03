import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateDimensionShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_indBotSC_shortExact

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.indBotSC_shortExact {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep.{u} k G)}
    (hX : X.ShortExact) : (Rep.indBotSC X).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_indBotSC_shortExact.solution
