import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_natCard_H1_eq_natCard_H2_of_finite

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.natCard_H1_eq_natCard_H2_of_finite
    {G : Type} [Group G] [Finite G] [IsCyclic G] (A : Rep ℤ G) [Finite A] :
    Finite (H1 A) ∧ Finite (H2 A) ∧ Nat.card (H1 A) = Nat.card (H2 A) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_natCard_H1_eq_natCard_H2_of_finite.solution
