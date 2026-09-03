import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import P2M.Util
import P2M.Sol.S_groupCohomology_subsingleton_H1_of_isUnit_card

universe u

open CategoryTheory
open CategoryTheory in
theorem groupCohomology.subsingleton_H1_of_isUnit_card
    {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (hG : IsUnit ((Fintype.card G : k))) :
    Subsingleton (groupCohomology.H1 A) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_subsingleton_H1_of_isUnit_card.solution
