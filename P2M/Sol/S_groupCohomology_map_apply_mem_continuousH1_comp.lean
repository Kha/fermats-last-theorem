import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
namespace P2MW.S_groupCohomology_map_apply_mem_continuousH1_comp
set_option autoImplicit false
open CategoryTheory groupCohomology
universe u

theorem solution
    {k G H : Type u} [CommRing k] [Group G] [Group H]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (loc : H →* G)
    (M : Rep.{u} k G) (x : H1 M) (hx : x ∈ continuousH1 r M) :
    (map loc (𝟙 (Rep.res loc M)) 1).hom x ∈ continuousH1 (r.comp loc) (Rep.res loc M) := by
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1_iff r M x).1 hx
  have hcomp : (map loc (𝟙 (Rep.res loc M)) 1).hom ((H1π M).hom c)
      = (H1π (Rep.res loc M)).hom (mapCocycles₁ loc (𝟙 (Rep.res loc M)) c) :=
    H1π_comp_map_apply loc (𝟙 (Rep.res loc M)) c
  rw [hcomp]
  refine H1π_mem_continuousH1 (r.comp loc) (Rep.res loc M) ?_
  obtain ⟨F, hF, hc⟩ := hc
  refine ⟨F, hF, fun h s hs => ?_⟩
  show c (loc (h * s)) = c (loc h)
  rw [map_mul]
  exact hc (loc h) (loc s) hs
