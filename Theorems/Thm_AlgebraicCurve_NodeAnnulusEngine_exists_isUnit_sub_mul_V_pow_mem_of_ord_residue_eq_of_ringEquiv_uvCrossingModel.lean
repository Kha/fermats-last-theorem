import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_NodeAnnulusEngine_exists_isUnit_sub_mul_V_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.NodeAnnulusEngine.exists_isUnit_sub_mul_V_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    (R₁ : RegularProlongation A F Fbar₁) (x₁ : Place (ResidueField A) Fbar₁)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (h𝒩₀ : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₁.integers)

    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A) (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)

    (x y : ↥𝒩₀)
    (hxU : ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
      ι (algebraMap ↥𝒩₀ _ x) - γ * U (π ^ E) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (hyV : ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
      ι (algebraMap ↥𝒩₀ _ y) - γ * V (π ^ E) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})

    (hker : ∀ f : ↥𝒩₀, R₁.residue ⟨f, h𝒩₀ f f.2⟩ = 0 ↔
      ι (algebraMap ↥𝒩₀ _ f) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hcent : ∀ f : ↥𝒩₀, ¬ IsUnit f → R₁.residue ⟨f, h𝒩₀ f f.2⟩ ≠ 0 → 0 < x₁.ord (R₁.residue ⟨f, h𝒩₀ f f.2⟩))
    (hx₁ : R₁.residue ⟨x, h𝒩₀ x x.2⟩ = 0)
    (hunif : x₁.ord (R₁.residue ⟨y, h𝒩₀ y y.2⟩) = 1) :
    ∀ (f : ↥𝒩₀) (n : ℕ), R₁.residue ⟨f, h𝒩₀ f f.2⟩ ≠ 0 →
      (0 ≤ x₁.ord (R₁.residue ⟨f, h𝒩₀ f f.2⟩)) ∧
      (x₁.ord (R₁.residue ⟨f, h𝒩₀ f f.2⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_isUnit_sub_mul_V_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel.solution
