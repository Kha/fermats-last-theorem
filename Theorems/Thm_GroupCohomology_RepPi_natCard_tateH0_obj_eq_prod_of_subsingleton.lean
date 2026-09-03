import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RepPi
import P2M.Util
import P2M.Sol.S_GroupCohomology_RepPi_natCard_tateH0_obj_eq_prod_of_subsingleton

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem GroupCohomology.RepPi.natCard_tateH0_obj_eq_prod_of_subsingleton {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) (s : Finset ι) (h : ∀ i, i ∉ s → Subsingleton (F i).tateH0) :
    Nat.card (GroupCohomology.RepPi.obj F).tateH0 = ∏ i ∈ s, Nat.card (F i).tateH0 := by p2m_exact_reverting @_root_.P2MW.S_GroupCohomology_RepPi_natCard_tateH0_obj_eq_prod_of_subsingleton.solution
