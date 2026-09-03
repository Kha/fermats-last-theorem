import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_tateMap_add

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.tateMap_add {k G : Type u} [CommRing k] [Group G] [Fintype G] {A B : Rep.{u} k G}
    (φ ψ : A ⟶ B) (n : ℤ) : Rep.tateMap (φ + ψ) n = Rep.tateMap φ n + Rep.tateMap ψ n := by p2m_exact_reverting @_root_.P2MW.S_Rep_tateMap_add.solution
