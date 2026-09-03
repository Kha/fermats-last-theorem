import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_map_inflationImage_le

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.map_inflationImage_le {k : Type u} [CommRing k] {G : Type u} [Group G] {Δ : Type u} [Group Δ] (f : Δ →* G) {M : Rep k G} {N : Rep k Δ}
    (φ : Rep.res f M ⟶ N) (T : Subgroup G) [T.Normal] (S : Subgroup Δ) [S.Normal]
    (hST : S ≤ T.comap f) :
    (inflationImage M T).map (groupCohomology.map f φ 1).hom ≤ inflationImage N S := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_map_inflationImage_le.solution
