import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_natCard_H2_trivial_int

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.natCard_H2_trivial_int
    {G : Type} [Group G] [Finite G] [IsCyclic G] :
    Nat.card (H2 (Rep.trivial ℤ G ℤ)) = Nat.card G := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_natCard_H2_trivial_int.solution
