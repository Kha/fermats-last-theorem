import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_groupCohomology_H1_subsingleton_of_isUnit_card

universe u
open CategoryTheory in
theorem groupCohomology.H1.subsingleton_of_isUnit_card
    {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (hG : IsUnit ((Fintype.card G : k))) :
    Subsingleton (groupCohomology.H1 A) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_H1_subsingleton_of_isUnit_card.solution
