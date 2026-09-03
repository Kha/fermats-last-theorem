import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import P2M.Util
import P2M.Sol.S_GroupCohomology_RepPi_isZero_groupCohomology_obj

set_option autoImplicit false
universe u
open CategoryTheory
theorem GroupCohomology.RepPi.isZero_groupCohomology_obj {k G ι : Type u} [CommRing k] [Group G]
    (F : ι → Rep.{u} k G) (n : ℕ) (h : ∀ i, CategoryTheory.Limits.IsZero (groupCohomology (F i) n)) :
    CategoryTheory.Limits.IsZero (groupCohomology (GroupCohomology.RepPi.obj F) n) := by p2m_exact_reverting @_root_.P2MW.S_GroupCohomology_RepPi_isZero_groupCohomology_obj.solution
