import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import P2M.Util
import P2M.Sol.S_groupCohomology_IsGradedCupProduct_unique

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory groupCohomology
theorem groupCohomology.IsGradedCupProduct.unique {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G)
    (cup cup' : groupCohomology.GradedCupFamily A B)
    (h : groupCohomology.IsGradedCupProduct A B cup) (h' : groupCohomology.IsGradedCupProduct A B cup') : cup = cup' := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_IsGradedCupProduct_unique.solution
