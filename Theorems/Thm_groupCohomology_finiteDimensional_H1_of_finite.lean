import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_finiteDimensional_H1_of_finite

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finiteDimensional_H1_of_finite {k : Type u} [Field k] {G : Type u} [Group G] [Finite G] (A : Rep k G) [FiniteDimensional k A] :
    FiniteDimensional k (H1 A) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finiteDimensional_H1_of_finite.solution
