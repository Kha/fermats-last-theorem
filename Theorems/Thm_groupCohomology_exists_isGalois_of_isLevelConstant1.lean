import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_isGalois_of_isLevelConstant1

set_option autoImplicit false

universe u
theorem groupCohomology.exists_isGalois_of_isLevelConstant1 {G : Type u} [Group G]
    {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {X : Type*} {f : G → X}
    (hf : groupCohomology.IsLevelConstant₁ r f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g ∧ f (s * g) = f g := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_isGalois_of_isLevelConstant1.solution
