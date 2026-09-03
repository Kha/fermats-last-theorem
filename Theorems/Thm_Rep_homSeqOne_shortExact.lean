import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_GroupCohomology_RelationHomDefect
import P2M.Util
import P2M.Sol.S_Rep_homSeqOne_shortExact

set_option autoImplicit false

open CategoryTheory
theorem Rep.homSeqOne_shortExact {G : Type} [Group G] (B E : Rep ℤ G) : (Rep.homSeq₁ B E).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_homSeqOne_shortExact.solution
