import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateResCor
import P2M.Util
import P2M.Sol.S_Rep_tateH0Cores_comp_tateH0Res

set_option autoImplicit false
universe u v w
open CategoryTheory Rep
theorem Rep.tateH0Cores_comp_tateH0Res {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] (A : Rep.{w} k G) :
    Rep.tateH0Cores S A ∘ₗ Rep.tateH0Res S A = (S.index : k) • LinearMap.id := by p2m_exact_reverting @_root_.P2MW.S_Rep_tateH0Cores_comp_tateH0Res.solution
