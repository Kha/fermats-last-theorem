import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_exact_tateMap_tateMap

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.exact_tateMap_tateMap {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    Function.Exact (Rep.tateMap X.f n).hom (Rep.tateMap X.g n).hom := by p2m_exact_reverting @_root_.P2MW.S_Rep_exact_tateMap_tateMap.solution
