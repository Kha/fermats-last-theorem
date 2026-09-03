import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_subsingleton_H1_trivial_int

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.subsingleton_H1_trivial_int
    {G : Type} [Group G] [Finite G] :
    Subsingleton (H1 (Rep.trivial ℤ G ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_subsingleton_H1_trivial_int.solution
