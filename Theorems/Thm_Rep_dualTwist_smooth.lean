import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_Rep_dualTwist_smooth

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.dualTwist_smooth {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep.{u} k G) [FiniteDimensional k M] (χ : G →* kˣ)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (hχ : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → χ s = 1) :
    ∀ f : M.dualTwist χ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → (M.dualTwist χ).ρ s f = f := by p2m_exact_reverting @_root_.P2MW.S_Rep_dualTwist_smooth.solution
