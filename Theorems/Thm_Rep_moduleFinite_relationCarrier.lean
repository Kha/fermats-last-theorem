import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Definitions.Def_GroupCohomology_RelationModule
import P2M.Util
import P2M.Sol.S_Rep_moduleFinite_relationCarrier

set_option autoImplicit false

open CategoryTheory Rep MonoidalCategory
theorem Rep.moduleFinite_relationCarrier {G : Type} [Group G] [Fintype G] (B : Rep ℤ G) [Fintype B] :
    Module.Finite ℤ (Rep.relationCarrier B) := by p2m_exact_reverting @_root_.P2MW.S_Rep_moduleFinite_relationCarrier.solution
