import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_GroupCohomology_RelationHomDefect
import P2M.Util
import P2M.Sol.S_GroupCohomology_RepImage_seq_shortExact

set_option autoImplicit false

open CategoryTheory
theorem GroupCohomology.RepImage.seq_shortExact {k G : Type} [CommRing k] [Group G] {X Y : Rep k G} (f : X ⟶ Y) :
    (GroupCohomology.RepImage.seq f).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_GroupCohomology_RepImage_seq_shortExact.solution
