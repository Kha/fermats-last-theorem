import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import P2M.Util
import P2M.Sol.S_groupCohomology_bijective_theta_of_mulEquiv

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.bijective_theta_of_mulEquiv
    {k G₁ G₂ : Type u} [CommRing k] [Group G₁] [Group G₂]
    (r₁ : G₁ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (r₂ : G₂ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (e : G₂ ≃* G₁) (he : ∀ g : G₂, r₁ (e.toMonoidHom g) = r₂ g)
    {M D N : Rep.{u} k G₁} (φ : M →ₗ[k] D →ₗ[k] N)
    (inv₂ : continuousH2 r₂ (Rep.res e.toMonoidHom N) →ₗ[k] k) (hinv₂ : Function.Bijective inv₂)
    (hG₁ : Function.Bijective (inv₂ ∘ₗ continuousH2Map (rH := r₁) (rG := r₂) (A := N) (B := Rep.res e.toMonoidHom N)
          e.toMonoidHom he LinearMap.id (fun _ _ => rfl)) →
      ∀ (θ₀ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r₁ D)),
        IsTheta0 r₁ φ (inv₂ ∘ₗ continuousH2Map (rH := r₁) (rG := r₂) (A := N) (B := Rep.res e.toMonoidHom N)
          e.toMonoidHom he LinearMap.id (fun _ _ => rfl)) θ₀ →
      ∀ (θ₁ : continuousH1 r₁ M →ₗ[k] Module.Dual k (continuousH1 r₁ D)),
        IsTheta1 r₁ φ (inv₂ ∘ₗ continuousH2Map (rH := r₁) (rG := r₂) (A := N) (B := Rep.res e.toMonoidHom N)
          e.toMonoidHom he LinearMap.id (fun _ _ => rfl)) θ₁ →
      ∀ (θ₂ : continuousH2 r₁ M →ₗ[k] Module.Dual k D.ρ.invariants),
        IsTheta2 r₁ φ (inv₂ ∘ₗ continuousH2Map (rH := r₁) (rG := r₂) (A := N) (B := Rep.res e.toMonoidHom N)
          e.toMonoidHom he LinearMap.id (fun _ _ => rfl)) θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (Θ₀ : (Rep.res e.toMonoidHom M).ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r₂ (Rep.res e.toMonoidHom D)))
    (hΘ₀ : IsTheta0 r₂ (φ : Rep.res e.toMonoidHom M →ₗ[k] Rep.res e.toMonoidHom D →ₗ[k] Rep.res e.toMonoidHom N) inv₂ Θ₀)
    (Θ₁ : continuousH1 r₂ (Rep.res e.toMonoidHom M) →ₗ[k] Module.Dual k (continuousH1 r₂ (Rep.res e.toMonoidHom D)))
    (hΘ₁ : IsTheta1 r₂ (φ : Rep.res e.toMonoidHom M →ₗ[k] Rep.res e.toMonoidHom D →ₗ[k] Rep.res e.toMonoidHom N) inv₂ Θ₁)
    (Θ₂ : continuousH2 r₂ (Rep.res e.toMonoidHom M) →ₗ[k] Module.Dual k (Rep.res e.toMonoidHom D).ρ.invariants)
    (hΘ₂ : IsTheta2 r₂ (φ : Rep.res e.toMonoidHom M →ₗ[k] Rep.res e.toMonoidHom D →ₗ[k] Rep.res e.toMonoidHom N) inv₂ Θ₂) :
    Function.Bijective Θ₀ ∧ Function.Bijective Θ₁ ∧ Function.Bijective Θ₂ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_bijective_theta_of_mulEquiv.solution
