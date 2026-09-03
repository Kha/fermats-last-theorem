import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import P2M.Util
import P2M.Sol.S_groupCohomology_bijective_theta_coind
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.bijective_theta_coind
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (U : Subgroup G) [U.FiniteIndex]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ U)
    {NU DU : Rep.{u} k U} {Nμ : Rep.{u} k G}
    (φU : NU →ₗ[k] DU →ₗ[k] Rep.res U.subtype Nμ) (hφU : Rep.IsEquivariantBilinear NU DU (Rep.res U.subtype Nμ) φU)
    (hsmDU : ∀ x : DU, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : U, (r.comp U.subtype) s ∈ F.fixingSubgroup → DU.ρ s x = x)
    (invU : continuousH2 (r.comp U.subtype) (Rep.res U.subtype Nμ) →ₗ[k] k) (invG : continuousH2 r Nμ →ₗ[k] k)
    (τ : Rep.coind U.subtype (Rep.res U.subtype Nμ) ⟶ Nμ)
    (hinv : ∀ (w : levelCocycles₂ r (Rep.coind U.subtype (Rep.res U.subtype Nμ)))
      (w₁ : levelCocycles₂ (r.comp U.subtype) (Rep.res U.subtype Nμ)),
      (∀ s t : U, (w₁ : U × U → Nμ) (s, t)
        = ((w : G × G → Rep.coind U.subtype (Rep.res U.subtype Nμ)) ((s : G), (t : G)) : G → Nμ) 1) →
      invG (continuousH2MapHom r τ (continuousH2π r _ w)) = invU (continuousH2π _ _ w₁))
    (Ψ : Rep.coind U.subtype NU →ₗ[k] Rep.coind U.subtype DU →ₗ[k] Nμ)
    (hΨ : ∀ (f : Rep.coind U.subtype NU) (g : Rep.coind U.subtype DU) (w : Rep.coind U.subtype (Rep.res U.subtype Nμ)),
      (∀ h : G, (w : G → Nμ) h = φU ((f : G → NU) h) ((g : G → DU) h)) → Ψ f g = τ.hom w)
    (θ₀ : NU.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 (r.comp U.subtype) DU)) (hθ₀ : IsTheta0 (r.comp U.subtype) φU invU θ₀)
    (θ₁ : continuousH1 (r.comp U.subtype) NU →ₗ[k] Module.Dual k (continuousH1 (r.comp U.subtype) DU))
    (hθ₁ : IsTheta1 (r.comp U.subtype) φU invU θ₁)
    (θ₂ : continuousH2 (r.comp U.subtype) NU →ₗ[k] Module.Dual k DU.ρ.invariants) (hθ₂ : IsTheta2 (r.comp U.subtype) φU invU θ₂)
    (Θ₀ : (Rep.coind U.subtype NU).ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r (Rep.coind U.subtype DU)))
    (hΘ₀ : IsTheta0 r Ψ invG Θ₀)
    (Θ₁ : continuousH1 r (Rep.coind U.subtype NU) →ₗ[k] Module.Dual k (continuousH1 r (Rep.coind U.subtype DU)))
    (hΘ₁ : IsTheta1 r Ψ invG Θ₁)
    (Θ₂ : continuousH2 r (Rep.coind U.subtype NU) →ₗ[k] Module.Dual k (Rep.coind U.subtype DU).ρ.invariants)
    (hΘ₂ : IsTheta2 r Ψ invG Θ₂)
    (hU' : Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂) :
    Function.Bijective Θ₀ ∧ Function.Bijective Θ₁ ∧ Function.Bijective Θ₂ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_bijective_theta_coind.solution
