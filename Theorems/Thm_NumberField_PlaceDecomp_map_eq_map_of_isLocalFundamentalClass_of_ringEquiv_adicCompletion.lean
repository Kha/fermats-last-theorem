import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
attribute [-instance] ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K))
    (q₁ : ℕ) [Fact q₁.Prime] (_ : ((q₁ : ℕ) : 𝓞 K) ∈ w.asIdeal) (L₁ : IntermediateField ℚ_[q₁] (PadicAlgCl q₁)) [FiniteDimensional ℚ_[q₁] L₁]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L₁] [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w)) L₁]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₁)ˣ]
    (Φ₁ : w.adicCompletion K ≃+* L₁)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q₁]), g • algebraMap ℚ_[q₁] L₁ y = algebraMap ℚ_[q₁] L₁ y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L₁)ˣ), ((g • y : (↥L₁)ˣ) : L₁) = g • (y : L₁))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ₁ (g • y) = g • Φ₁ y)
    (K₀₁ : IntermediateField ℚ_[q₁] (PadicAlgCl q₁)) [FiniteDimensional ℚ_[q₁] K₀₁]
    (_ : ExtCitation.LocalLevel.IsBase q₁ L₁ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₁)
    (θ₁ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₁)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (_ : ∀ y : (↥L₁)ˣ, ((Additive.toMul ((θ₁).hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = (Φ₁).symm (y : L₁))
    (u₁ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₁)ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q₁ L₁ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₁ u₁)
    (q₂ : ℕ) [Fact q₂.Prime] (_ : ((q₂ : ℕ) : 𝓞 K) ∈ w.asIdeal) (L₂ : IntermediateField ℚ_[q₂] (PadicAlgCl q₂)) [FiniteDimensional ℚ_[q₂] L₂]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L₂] [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w)) L₂]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₂)ˣ]
    (Φ₂ : w.adicCompletion K ≃+* L₂)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q₂]), g • algebraMap ℚ_[q₂] L₂ y = algebraMap ℚ_[q₂] L₂ y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L₂)ˣ), ((g • y : (↥L₂)ˣ) : L₂) = g • (y : L₂))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ₂ (g • y) = g • Φ₂ y)
    (K₀₂ : IntermediateField ℚ_[q₂] (PadicAlgCl q₂)) [FiniteDimensional ℚ_[q₂] K₀₂]
    (_ : ExtCitation.LocalLevel.IsBase q₂ L₂ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₂)
    (θ₂ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₂)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (_ : ∀ y : (↥L₂)ˣ, ((Additive.toMul ((θ₂).hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = (Φ₂).symm (y : L₂))
    (u₂ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₂)ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q₂ L₂ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₂ u₂) :
    (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ₁ 2).hom u₁ =
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ₂ 2).hom u₂ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.solution
