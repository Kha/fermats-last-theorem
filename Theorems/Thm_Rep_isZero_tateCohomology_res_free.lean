import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Definitions.Def_GroupCohomology_RelationModule
import P2M.Util
import P2M.Sol.S_Rep_isZero_tateCohomology_res_free

set_option autoImplicit false

open CategoryTheory Rep MonoidalCategory
theorem Rep.isZero_tateCohomology_res_free {k G : Type} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] (α : Type) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.res S.subtype (Rep.free k G α)).tateCohomology q) := by p2m_exact_reverting @_root_.P2MW.S_Rep_isZero_tateCohomology_res_free.solution
