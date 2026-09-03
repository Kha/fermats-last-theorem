import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2
import P2M.Util
import P2M.Sol.S_groupCohomology_eq_zero_of_map_res_two_eq_zero_of_coprime

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.eq_zero_of_map_res_two_eq_zero_of_coprime
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex]
    {p n : ℕ} (hcop : H.index.Coprime p) (x : H2 A) (hp : p ^ n • x = 0)
    (hres : (map H.subtype (𝟙 (Rep.res H.subtype A)) 2).hom x = 0) : x = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_eq_zero_of_map_res_two_eq_zero_of_coprime.solution
