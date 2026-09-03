import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_theta0_and_theta2

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.exists_theta0_and_theta2
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D N : Rep.{u} k G} (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (inv : continuousH2 r N →ₗ[k] k) :
    (∃ θ₀ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D), IsTheta0 r φ inv θ₀) ∧
    (∃ θ₂ : continuousH2 r M →ₗ[k] Module.Dual k D.ρ.invariants, IsTheta2 r φ inv θ₂) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_theta0_and_theta2.solution
