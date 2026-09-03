import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import P2M.Util
import P2M.Sol.S_Rep_exists_isTateCupProduct
attribute [-simp] Rep.coe_dimShiftDownObjMap_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.exists_isTateCupProduct {k G : Type u} [CommRing k] [Group G] [Fintype G] :
    ∃ cup : Rep.TateCupFamily k G, Rep.IsTateCupProduct cup := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_isTateCupProduct.solution
