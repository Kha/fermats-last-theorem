import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain
p2m_open "scoped NumberField.PlaceDecomp NumberField.PlaceTransport~transport_trans_transport~transport_eq_actRingEquiv"

theorem NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_map_of_smul_eq
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (hσ : σ • w = w₁)

    (c : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* ↥(NumberField.PlaceDecomp.decomp E F w))
    (hc : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w₁), ((c τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ)
    (T : Rep.res c (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)
    (hT : ∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (T.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
      NumberField.PlaceTransport.transport σ hσ (x : w.adicCompletion F))

    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L']
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
    (Φ : w.adicCompletion F ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : w.adicCompletion F), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (_ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : L'))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp E F w₁) = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
    ∃ (_ : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) L')
      (_ : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (↥L')ˣ)
      (Φ₁ : w₁.adicCompletion F ≃+* L')
      (θ₁ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (↥L')ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)
      (u₁ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (↥L')ˣ)),
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w₁)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y) ∧
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w₁)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L')) ∧
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w₁)) (y : w₁.adicCompletion F), Φ₁ (g • y) = g • Φ₁ y) ∧
      ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w₁)) K₀ ∧
      (∀ y : (↥L')ˣ, ((Additive.toMul (θ₁.hom (Additive.ofMul y)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) = Φ₁.symm (y : L')) ∧
      ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w₁)) K₀ u₁ ∧
      (groupCohomology.map c T 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u) =
        (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w₁)) θ₁ 2).hom u₁ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq.solution
