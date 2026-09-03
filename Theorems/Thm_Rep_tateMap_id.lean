import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_tateMap_id

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.tateMap_id {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (n : ℤ) :
    Rep.tateMap (𝟙 A) n = 𝟙 (A.tateCohomology n) := by p2m_exact_reverting @_root_.P2MW.S_Rep_tateMap_id.solution
