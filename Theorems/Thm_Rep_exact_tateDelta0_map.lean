import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import P2M.Util
import P2M.Sol.S_Rep_exact_tateDelta0_map

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.exact_tateDelta0_map {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateδ₀ hX) ((groupCohomology.functor k G 1).map X.f).hom := by p2m_exact_reverting @_root_.P2MW.S_Rep_exact_tateDelta0_map.solution
