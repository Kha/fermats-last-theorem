import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Theorems.Thm_groupCohomology_map_inflationImage_le
import P2M.Util
namespace P2MW.S_groupCohomology_inflationImage_antitone

open CategoryTheory Module groupCohomology

universe u

theorem solution {k : Type u} [CommRing k] {G : Type u} [Group G] (M : Rep k G) {S T : Subgroup G} [S.Normal] [T.Normal]
    (hST : S ≤ T) : inflationImage M T ≤ inflationImage M S := by
  have h := map_inflationImage_le (MonoidHom.id G) (𝟙 M) T S
    (by simpa using hST)
  rw [groupCohomology.map_id] at h
  simpa using h
