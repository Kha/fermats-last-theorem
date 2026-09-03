import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import P2M.Util
import P2M.Sol.S_Rep_exact_tateH0Map_tateDelta0

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.exact_tateH0Map_tateDelta0 {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateH0Map X.g) (Rep.tateδ₀ hX) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exact_tateH0Map_tateDelta0.solution
