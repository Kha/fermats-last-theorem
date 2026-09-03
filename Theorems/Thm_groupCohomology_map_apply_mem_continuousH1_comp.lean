import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_map_apply_mem_continuousH1_comp
set_option autoImplicit false
open CategoryTheory groupCohomology
universe u
theorem groupCohomology.map_apply_mem_continuousH1_comp
    {k G H : Type u} [CommRing k] [Group G] [Group H]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (loc : H →* G)
    (M : Rep.{u} k G) (x : H1 M) (hx : x ∈ continuousH1 r M) :
    (map loc (𝟙 (Rep.res loc M)) 1).hom x ∈ continuousH1 (r.comp loc) (Rep.res loc M) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_map_apply_mem_continuousH1_comp.solution
