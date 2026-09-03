import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_inflationImage_antitone

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.inflationImage_antitone {k : Type u} [CommRing k] {G : Type u} [Group G] (M : Rep k G) {S T : Subgroup G} [S.Normal] [T.Normal]
    (hST : S ≤ T) : inflationImage M T ≤ inflationImage M S := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_inflationImage_antitone.solution
