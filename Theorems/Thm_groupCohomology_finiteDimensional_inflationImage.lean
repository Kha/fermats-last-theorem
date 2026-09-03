import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_finiteDimensional_inflationImage

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finiteDimensional_inflationImage {k : Type u} [Field k] {G : Type u} [Group G] (M : Rep k G) (S : Subgroup G) [S.Normal]
    [S.FiniteIndex] [FiniteDimensional k M] :
    FiniteDimensional k (inflationImage M S) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finiteDimensional_inflationImage.solution
