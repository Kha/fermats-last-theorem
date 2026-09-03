import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import P2M.Util
import P2M.Sol.S_GroupCohomology_RepPi_bijective_pi_map_proj

set_option autoImplicit false

open CategoryTheory
theorem GroupCohomology.RepPi.bijective_pi_map_proj {k G : Type} [CommRing k] [Group G] {ι : Type}
    (F : ι → Rep k G) (n : ℕ) :
    Function.Bijective (fun x : groupCohomology (GroupCohomology.RepPi.obj F) n =>
      fun i : ι => (groupCohomology.map (MonoidHom.id G) (GroupCohomology.RepPi.proj F i) n).hom x) := by p2m_exact_reverting @_root_.P2MW.S_GroupCohomology_RepPi_bijective_pi_map_proj.solution
