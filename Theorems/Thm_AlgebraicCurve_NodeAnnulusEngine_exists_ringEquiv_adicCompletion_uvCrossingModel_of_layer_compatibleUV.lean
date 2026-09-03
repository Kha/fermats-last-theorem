import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_NodeAnnulusEngine_exists_ringEquiv_adicCompletion_uvCrossingModel_of_layer_compatibleUV
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal instTopologicallyFGOfFiniteType

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.NodeAnnulusEngine.exists_ringEquiv_adicCompletion_uvCrossingModel_of_layer_compatibleUV
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (ϖ : L) (hϖ𝒩₀ : algebraMap L F ϖ ∈ 𝒩₀)

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F ϖ, hϖ𝒩₀⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)

    (x y : F) (hx : x ∈ 𝒩₀) (hy : y ∈ 𝒩₀)
    (hιx : ∃ β : UVCrossingModel W (π ^ E), IsUnit β ∧
      ι (algebraMap ↥𝒩₀ _ ⟨x, hx⟩) - U (π ^ E) * β ∈ Ideal.span {const (π ^ E) π})
    (hιy : ∃ β : UVCrossingModel W (π ^ E), IsUnit β ∧
      ι (algebraMap ↥𝒩₀ _ ⟨y, hy⟩) - V (π ^ E) * β ∈ Ideal.span {const (π ^ E) π})

    (C' : Subring L) (ϖ' : ↥C')
    (e : ℕ) (hϖe : ∃ v : L, v ∈ C' ∧ v⁻¹ ∈ C' ∧ ϖ = v * ((ϖ' : ↥C') : L) ^ e)

    (𝒩₀' : Subring F) [IsLocalRing ↥𝒩₀'] [IsNoetherianRing ↥𝒩₀'] (h01 : 𝒩₀ ≤ 𝒩₀')
    (hloc : ∀ f : ↥𝒩₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion h01 f))
    (hC'mem : ∀ c : L, c ∈ C' → algebraMap L F c ∈ 𝒩₀')
    (hres' : ∀ g : ↥𝒩₀', ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ 𝒩₀'), ¬ IsUnit (g - ⟨_, h⟩))
    (hgen' : maximalIdeal ↥𝒩₀' ≤ (maximalIdeal ↥𝒩₀).map (Subring.inclusion h01) ⊔
      Ideal.span {⟨algebraMap L F (ϖ' : L), hC'mem _ ϖ'.2⟩})
    (hdim : 2 ≤ ringKrullDim ↥𝒩₀')

    {W' : Type*} [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] [IsAdicComplete (maximalIdeal W') W']
    (π' : W') (hπ' : Irreducible π') (j : ↥C' →+* W') (hjϖ : j ϖ' = π')
    (hjinj : ∀ (n : ℕ) (c : ↥C'), j c ∈ Ideal.span {π' ^ n} → c ∈ Ideal.span {ϖ' ^ n})
    (hjsur : ∀ (n : ℕ) (w : W'), ∃ c : ↥C', w - j c ∈ Ideal.span {π' ^ n}) :
    ∃ (σ' : W' →+* AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')
      (ι' : AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀' ≃+* UVCrossingModel W' (π' ^ (e * E))),

      (∀ c : ↥C', σ' (j c) = algebraMap ↥𝒩₀' _ ⟨algebraMap L F (c : L), hC'mem _ c.2⟩) ∧
      (∀ o : W', ι' (σ' o) = const (π' ^ (e * E)) o) ∧

      maximalIdeal ↥𝒩₀' =
        Ideal.span {⟨algebraMap L F (ϖ' : L), hC'mem _ ϖ'.2⟩, ⟨x, h01 hx⟩, ⟨y, h01 hy⟩} ∧

      (∃ β : UVCrossingModel W' (π' ^ (e * E)), IsUnit β ∧
        ι' (algebraMap ↥𝒩₀' _ ⟨x, h01 hx⟩) - U (π' ^ (e * E)) * β ∈ Ideal.span {const (π' ^ (e * E)) π'}) ∧
      (∃ β : UVCrossingModel W' (π' ^ (e * E)), IsUnit β ∧
        ι' (algebraMap ↥𝒩₀' _ ⟨y, h01 hy⟩) - V (π' ^ (e * E)) * β ∈ Ideal.span {const (π' ^ (e * E)) π'}) ∧

      (∃ (θ : UVCrossingModel W (π ^ E) →+* UVCrossingModel W' (π' ^ (e * E))) (βU βV : UVCrossingModel W' (π' ^ (e * E))), IsUnit βU ∧ IsUnit βV ∧
        θ (U (π ^ E)) = βU * U (π' ^ (e * E)) ∧
        θ (V (π ^ E)) = βV * V (π' ^ (e * E)) ∧
        (∀ (f : F) (hf : f ∈ 𝒩₀), ι' (algebraMap ↥𝒩₀' _ ⟨f, h01 hf⟩) = θ (ι (algebraMap ↥𝒩₀ _ ⟨f, hf⟩)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_ringEquiv_adicCompletion_uvCrossingModel_of_layer_compatibleUV.solution
