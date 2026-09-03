import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2
import P2M.Util
import P2M.Sol.S_groupCohomology_Cores_cores_map_res_eq_index_smul

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.Cores.cores_map_res_eq_index_smul
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex] (τ : Cores.Transversal H) (x : H2 A) :
    Cores.cores A τ ((map H.subtype (𝟙 (Rep.res H.subtype A)) 2).hom x) = H.index • x := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Cores_cores_map_res_eq_index_smul.solution
