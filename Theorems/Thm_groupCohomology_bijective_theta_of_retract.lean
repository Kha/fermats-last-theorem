import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import P2M.Util
import P2M.Sol.S_groupCohomology_bijective_theta_of_retract

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.bijective_theta_of_retract
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D M₁ D₁ N : Rep.{u} k G}
    (φ : M →ₗ[k] D →ₗ[k] N)
    (φ₁ : M₁ →ₗ[k] D₁ →ₗ[k] N) (hφ₁ : Rep.IsEquivariantBilinear M₁ D₁ N φ₁)
    (a : M ⟶ M₁) (b : M₁ ⟶ M) (hba : ∀ m : M, b.hom (a.hom m) = m)
    (a' : D₁ ⟶ D) (b' : D ⟶ D₁) (hab' : ∀ x : D, a'.hom (b'.hom x) = x)
    (ha : ∀ (m : M) (y : D₁), φ₁ (a.hom m) y = φ m (a'.hom y))
    (hb : ∀ (x : M₁) (d : D), φ (b.hom x) d = φ₁ x (b'.hom d))
    (hsmD : ∀ x : D, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → D.ρ s x = x)
    (inv : continuousH2 r N →ₗ[k] k)
    (θ₀ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D)) (hθ₀ : IsTheta0 r φ inv θ₀)
    (θ₁ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D)) (hθ₁ : IsTheta1 r φ inv θ₁)
    (θ₂ : continuousH2 r M →ₗ[k] Module.Dual k D.ρ.invariants) (hθ₂ : IsTheta2 r φ inv θ₂)
    (Θ₀ : M₁.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D₁)) (hΘ₀ : IsTheta0 r φ₁ inv Θ₀)
    (Θ₁ : continuousH1 r M₁ →ₗ[k] Module.Dual k (continuousH1 r D₁)) (hΘ₁ : IsTheta1 r φ₁ inv Θ₁)
    (Θ₂ : continuousH2 r M₁ →ₗ[k] Module.Dual k D₁.ρ.invariants) (hΘ₂ : IsTheta2 r φ₁ inv Θ₂)
    (h₁ : Function.Bijective Θ₀ ∧ Function.Bijective Θ₁ ∧ Function.Bijective Θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_bijective_theta_of_retract.solution
