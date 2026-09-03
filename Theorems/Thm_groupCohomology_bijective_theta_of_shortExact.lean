import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import P2M.Util
import P2M.Sol.S_groupCohomology_bijective_theta_of_shortExact

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.bijective_theta_of_shortExact
    {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M' M M'' D'' D D' N : Rep.{u} k G}
    (i : M' ⟶ M) (π : M ⟶ M'') (hi : Function.Injective i.hom) (hπ : Function.Surjective π.hom)
    (hex : ∀ m : M, π.hom m = 0 ↔ ∃ m' : M', i.hom m' = m)
    (πD : D'' ⟶ D) (iD : D ⟶ D') (hπD : Function.Injective πD.hom) (hiD : Function.Surjective iD.hom)
    (hexD : ∀ x : D, iD.hom x = 0 ↔ ∃ y : D'', πD.hom y = x)
    (hsmM : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (hsmD : ∀ x : D, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → D.ρ s x = x)
    (φ' : M' →ₗ[k] D' →ₗ[k] N)
    (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (φ'' : M'' →ₗ[k] D'' →ₗ[k] N)
    (hcompat_i : ∀ (m' : M') (x : D), φ (i.hom m') x = φ' m' (iD.hom x))
    (hcompat_π : ∀ (m : M) (y : D''), φ m (πD.hom y) = φ'' (π.hom m) y)
    (inv : continuousH2 r N →ₗ[k] k)
    (hD2π : Function.Surjective (continuousH2MapHom r π))
    (hD2iD : Function.Surjective (continuousH2MapHom r iD))
    (θ₀' : M'.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D')) (hθ₀' : IsTheta0 r φ' inv θ₀')
    (θ₁' : continuousH1 r M' →ₗ[k] Module.Dual k (continuousH1 r D')) (hθ₁' : IsTheta1 r φ' inv θ₁')
    (θ₂' : continuousH2 r M' →ₗ[k] Module.Dual k D'.ρ.invariants) (hθ₂' : IsTheta2 r φ' inv θ₂')
    (θ₀ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D)) (hθ₀ : IsTheta0 r φ inv θ₀)
    (θ₁ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D)) (hθ₁ : IsTheta1 r φ inv θ₁)
    (θ₂ : continuousH2 r M →ₗ[k] Module.Dual k D.ρ.invariants) (hθ₂ : IsTheta2 r φ inv θ₂)
    (θ₀'' : M''.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D'')) (hθ₀'' : IsTheta0 r φ'' inv θ₀'')
    (θ₁'' : continuousH1 r M'' →ₗ[k] Module.Dual k (continuousH1 r D'')) (hθ₁'' : IsTheta1 r φ'' inv θ₁'')
    (θ₂'' : continuousH2 r M'' →ₗ[k] Module.Dual k D''.ρ.invariants) (hθ₂'' : IsTheta2 r φ'' inv θ₂'')
    (h' : Function.Bijective θ₀' ∧ Function.Bijective θ₁' ∧ Function.Bijective θ₂')
    (h'' : Function.Bijective θ₀'' ∧ Function.Bijective θ₁'' ∧ Function.Bijective θ₂'') :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_bijective_theta_of_shortExact.solution
