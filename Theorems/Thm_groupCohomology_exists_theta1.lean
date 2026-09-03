import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_theta1

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.exists_theta1
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D N : Rep.{u} k G} (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (hsmD : ∀ x : D, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → D.ρ s x = x)
    (inv : continuousH2 r N →ₗ[k] k) :
    ∃ θ₁ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D), IsTheta1 r φ inv θ₁ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_theta1.solution
