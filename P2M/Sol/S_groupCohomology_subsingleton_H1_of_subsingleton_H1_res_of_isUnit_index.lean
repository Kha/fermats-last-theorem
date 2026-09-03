import Mathlib
import Theorems.Thm_groupCohomology_injective_H1_restriction_of_isUnit_index
import P2M.Util
namespace P2MW.S_groupCohomology_subsingleton_H1_of_subsingleton_H1_res_of_isUnit_index

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {S : Subgroup G} [S.Normal]
    [Fintype (G ⧸ S)] (hindex : IsUnit ((Fintype.card (G ⧸ S) : k)))
    (hS : Subsingleton (H1 (Rep.res S.subtype A))) :
    Subsingleton (H1 A) := by
  haveI h₃ : Subsingleton ((H1InfRes A S).X₃ : Type u) := hS
  exact ⟨fun a b => injective_H1_restriction_of_isUnit_index hindex (Subsingleton.elim _ _)⟩
