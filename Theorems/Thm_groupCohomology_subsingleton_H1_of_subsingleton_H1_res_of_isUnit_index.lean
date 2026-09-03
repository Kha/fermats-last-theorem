import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_subsingleton_H1_of_subsingleton_H1_res_of_isUnit_index

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.subsingleton_H1_of_subsingleton_H1_res_of_isUnit_index {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {S : Subgroup G} [S.Normal]
    [Fintype (G ⧸ S)] (hindex : IsUnit ((Fintype.card (G ⧸ S) : k)))
    (hS : Subsingleton (H1 (Rep.res S.subtype A))) :
    Subsingleton (H1 A) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_subsingleton_H1_of_subsingleton_H1_res_of_isUnit_index.solution
