import Mathlib
import P2M.Util
namespace P2MW.S_groupCohomology_finiteDimensional_H1_of_finite

open CategoryTheory Module groupCohomology

universe u

theorem solution {k : Type u} [Field k] {G : Type u} [Group G] [Finite G] (A : Rep k G) [FiniteDimensional k A] :
    FiniteDimensional k (H1 A) := by
  have : FiniteDimensional k (G → A) := Module.Finite.pi
  have : FiniteDimensional k (cocycles₁ A) := FiniteDimensional.finiteDimensional_submodule _
  exact Module.Finite.of_surjective (ModuleCat.Hom.hom (H1π A))
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
