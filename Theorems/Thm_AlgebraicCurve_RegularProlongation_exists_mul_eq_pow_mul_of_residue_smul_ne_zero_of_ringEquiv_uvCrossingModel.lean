import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.RegularProlongation.exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (h𝒩₀R : ∀ f : F, f ∈ 𝒩₀ → f ∈ R.integers)
    (ϖ : L) (hϖ0 : ϖ ≠ 0) (hϖA : ϖ ∈ A) (hϖm : IsLocalRing.residue ↥A ⟨ϖ, hϖA⟩ = 0)
    (hϖN : algebraMap L F ϖ ∈ 𝒩₀)
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F ϖ, hϖN⟩) = const (π ^ E) π)
    (p s : ↥𝒩₀) (hp0 : p ≠ 0) (hp : R.residue ⟨(p : F), h𝒩₀R p p.2⟩ = 0)
    (hs : R.residue ⟨(s : F), h𝒩₀R s s.2⟩ ≠ 0) (hsu : ¬ IsUnit s)
    (a : ↥𝒩₀) (e : L) (h : e • (a : F) ∈ R.integers) (hne : R.residue ⟨e • (a : F), h⟩ ≠ 0) :
    ∃ (g : ℕ) (a₁ a₂ : ↥𝒩₀),
      R.residue ⟨(a₁ : F), h𝒩₀R a₁ a₁.2⟩ ≠ 0 ∧ R.residue ⟨(a₂ : F), h𝒩₀R a₂ a₂.2⟩ ≠ 0 ∧
      a * a₂ = ⟨algebraMap L F ϖ, hϖN⟩ ^ g * a₁ ∧
      ∃ hu : e * ϖ ^ g ∈ A, IsUnit (⟨e * ϖ ^ g, hu⟩ : ↥A) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel.solution
