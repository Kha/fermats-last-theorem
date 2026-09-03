import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_isLocalHom_of_layer
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal instTopologicallyFGOfFiniteType

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_isLocalHom_of_layer

    {N₀ : Type*} [CommRing N₀] [IsLocalRing N₀] [IsNoetherianRing N₀]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal N₀) N₀)
    (ϖ : N₀) (hσπ : σ π = algebraMap N₀ (AdicCompletion (maximalIdeal N₀) N₀) ϖ)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal N₀) N₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)

    {N₁ : Type*} [CommRing N₁] [IsLocalRing N₁] [IsNoetherianRing N₁]
    (f : N₀ →+* N₁) [IsLocalHom f]
    {C' : Type*} [CommRing C'] (c' : C' →+* N₁) (ϖ' : C')
    (e : ℕ) (hϖe : ∃ v : N₁, IsUnit v ∧ f ϖ = v * c' ϖ' ^ e)
    (hres' : ∀ g : N₁, ∃ o : C', ¬ IsUnit (g - c' o))
    (hgen' : maximalIdeal N₁ ≤ (maximalIdeal N₀).map f ⊔ Ideal.span {c' ϖ'})
    (hdim : 2 ≤ ringKrullDim N₁)

    {W' : Type*} [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] [IsAdicComplete (maximalIdeal W') W']
    (π' : W') (hπ' : Irreducible π') (j : C' →+* W') (hjϖ : j ϖ' = π')
    (hjinj : ∀ (n : ℕ) (c : C'), j c ∈ Ideal.span {π' ^ n} → c ∈ Ideal.span {ϖ' ^ n})
    (hjsur : ∀ (n : ℕ) (w : W'), ∃ c : C', w - j c ∈ Ideal.span {π' ^ n}) :
    ∃ (σ' : W' →+* AdicCompletion (maximalIdeal N₁) N₁)
      (ι' : AdicCompletion (maximalIdeal N₁) N₁ ≃+* UVCrossingModel W' (π' ^ (e * E))),
      (∀ c : C', σ' (j c) = algebraMap N₁ (AdicCompletion (maximalIdeal N₁) N₁) (c' c)) ∧
      (∀ o : W', ι' (σ' o) = const (π' ^ (e * E)) o) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_isLocalHom_of_layer.solution
