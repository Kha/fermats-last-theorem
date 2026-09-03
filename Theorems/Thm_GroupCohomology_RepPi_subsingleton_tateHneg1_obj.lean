import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RepPi
import P2M.Util
import P2M.Sol.S_GroupCohomology_RepPi_subsingleton_tateHneg1_obj

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem GroupCohomology.RepPi.subsingleton_tateHneg1_obj {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) (h : ∀ i, Subsingleton (F i).tateHneg1) :
    Subsingleton (GroupCohomology.RepPi.obj F).tateHneg1 := by p2m_exact_reverting @_root_.P2MW.S_GroupCohomology_RepPi_subsingleton_tateHneg1_obj.solution
