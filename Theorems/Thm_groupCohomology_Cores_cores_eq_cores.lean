import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2
import P2M.Util
import P2M.Sol.S_groupCohomology_Cores_cores_eq_cores

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.Cores.cores_eq_cores
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex]
    (τ τ' : Cores.Transversal H) (x : H2 (Rep.res H.subtype A)) :
    Cores.cores A τ x = Cores.cores A τ' x := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Cores_cores_eq_cores.solution
