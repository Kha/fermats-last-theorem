import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import P2M.Util
import P2M.Sol.S_Rep_exact_map_tateDeltaNeg2

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.exact_map_tateDeltaNeg2 {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact ((groupHomology.functor k G 1).map X.g).hom (Rep.tateδneg2 hX) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exact_map_tateDeltaNeg2.solution
