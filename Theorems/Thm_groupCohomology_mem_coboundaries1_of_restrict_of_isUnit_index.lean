import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_mem_coboundaries1_of_restrict_of_isUnit_index

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.mem_coboundaries1_of_restrict_of_isUnit_index
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G)
    [S.FiniteIndex] (hindex : IsUnit ((S.index : k)))
    (c : cocycles₁ A) (hc : ∃ a : A, ∀ s : S, c (s : G) = A.ρ (s : G) a - a) :
    ∃ a : A, ∀ g : G, c g = A.ρ g a - a := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_mem_coboundaries1_of_restrict_of_isUnit_index.solution
