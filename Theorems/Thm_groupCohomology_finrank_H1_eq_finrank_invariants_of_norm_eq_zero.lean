import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero

universe u

open CategoryTheory Module
theorem groupCohomology.finrank_H1_eq_finrank_invariants_of_norm_eq_zero
    {k G : Type u} [Field k] [Group G] (A : Rep k G) [Fintype G] [FiniteDimensional k A]
    {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (hN : A.ρ.norm = 0) :
    finrank k (groupCohomology.H1 A) = finrank k A.ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero.solution
