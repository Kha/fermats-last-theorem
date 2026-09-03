import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import P2M.Util
import P2M.Sol.S_Rep_exists_level_coind_apply_eq_self

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.exists_level_coind_apply_eq_self {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G) [S.FiniteIndex]
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, r s ∈ F.fixingSubgroup → N.ρ s n = n)
    (f : Rep.coind S.subtype N) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ u : G, r u ∈ F.fixingSubgroup → (Rep.coind S.subtype N).ρ u f = f := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_level_coind_apply_eq_self.solution
