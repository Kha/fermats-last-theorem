import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_etale_of_isLocalRing_of_isAdicComplete

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_of_etale_of_isLocalRing_of_isAdicComplete
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 0 < E)
    (R₀ : Type u) [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    (e₀ : R₀ ≃+* UVCrossingModel W (π ^ E))
    (B₁ : Type u) [CommRing B₁] [IsLocalRing B₁] [Algebra R₀ B₁] [Module.Finite R₀ B₁]
    [FaithfulSMul R₀ B₁] [Algebra.Etale R₀ B₁] :
    ∃ (W' : Type u) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W') W') (σ' : W →+* W')
      (_ : IsLocalRing.maximalIdeal W' = Ideal.span {σ' π})
      (e : B₁ ≃+* UVCrossingModel W' ((σ' π) ^ E)),
      (∀ (r : R₀) (w : W), e₀ r = const (π ^ E) w →
          e (algebraMap R₀ B₁ r) = const ((σ' π) ^ E) (σ' w)) ∧
      (∀ b : B₁, ∃ w' : W', b - e.symm (const ((σ' π) ^ E) w') ∈ IsLocalRing.maximalIdeal B₁) ∧
      e (algebraMap R₀ B₁ (e₀.symm (U (π ^ E)))) = U ((σ' π) ^ E) ∧
      e (algebraMap R₀ B₁ (e₀.symm (V (π ^ E)))) = V ((σ' π) ^ E) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_etale_of_isLocalRing_of_isAdicComplete.solution
