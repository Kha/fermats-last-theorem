import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Definitions.Def_GroupCohomology_RelationModule
import P2M.Util
import P2M.Sol.S_Rep_relationSeqInt_shortExact

set_option autoImplicit false

open CategoryTheory Rep MonoidalCategory
theorem Rep.relationSeqInt_shortExact {G : Type} [Group G] (B : Rep ℤ G) :
    (Rep.relationSeqInt B).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_relationSeqInt_shortExact.solution
