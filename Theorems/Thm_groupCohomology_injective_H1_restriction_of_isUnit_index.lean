import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_groupCohomology_injective_H1_restriction_of_isUnit_index

universe u

open CategoryTheory
theorem groupCohomology.injective_H1_restriction_of_isUnit_index
    {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {S : Subgroup G} [S.Normal]
    [Fintype (G ⧸ S)] (hindex : IsUnit ((Fintype.card (G ⧸ S) : k))) :
    Function.Injective (ModuleCat.Hom.hom (groupCohomology.H1InfRes A S).g) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_injective_H1_restriction_of_isUnit_index.solution
