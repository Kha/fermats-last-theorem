import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_isGradedCupProduct

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory groupCohomology
theorem groupCohomology.exists_isGradedCupProduct {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) :
    ∃ cup : groupCohomology.GradedCupFamily A B, groupCohomology.IsGradedCupProduct A B cup := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_isGradedCupProduct.solution
