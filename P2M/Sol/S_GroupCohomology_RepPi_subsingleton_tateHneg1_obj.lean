import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RepPi
import Theorems.Thm_GroupCohomology_RepPi_nonempty_tateHneg1_obj_linearEquiv
import P2M.Util
namespace P2MW.S_GroupCohomology_RepPi_subsingleton_tateHneg1_obj

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) (h : ∀ i, Subsingleton (F i).tateHneg1) :
    Subsingleton (GroupCohomology.RepPi.obj F).tateHneg1 := by
  obtain ⟨e⟩ := GroupCohomology.RepPi.nonempty_tateHneg1_obj_linearEquiv F
  exact e.toEquiv.subsingleton_congr.2 inferInstance
