import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower
attribute [-simp] IsLocalRing.principalUnits_zero
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    (W : HeightOneSpectrum (𝓞 M))
    (hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E M W))
    (hsolv₁ : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))

    (r : ↥(NumberField.PlaceDecomp.decomp E M W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
    (hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : F),
      algebraMap F M (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : M ≃ₐ[E] M) (algebraMap F M x))
    (iD : Rep.res r (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hiD : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
      ((Additive.toMul (iD.hom (Additive.ofMul x)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) (x : (W.under (𝓞 F)).adicCompletion F))

    (q : ℕ) [Fact q.Prime] (L L'' : IntermediateField ℚ_[q] (PadicAlgCl q)) (hLL'' : L ≤ L'')
    [FiniteDimensional ℚ_[q] L] [FiniteDimensional ℚ_[q] L'']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) L]
    [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) L]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L)ˣ]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E M W)) L''] [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E M W)) L'']
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L'')ˣ]
    (Φ : (W.under (𝓞 F)).adicCompletion F ≃+* L) (Φ'' : W.adicCompletion M ≃+* L'')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (x : (W.under (𝓞 F)).adicCompletion F), Φ (g • x) = g • Φ x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : W.adicCompletion M), Φ'' (g • x) = g • Φ'' x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (u : (↥L'')ˣ), ((g • u : (↥L'')ˣ) : L'') = g • (u : L''))
    (_ : ∀ x : (W.under (𝓞 F)).adicCompletion F,
      ((Φ'' (HeightOneSpectrum.Extension.adicCompletionSemialgHom F M
          (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) x) : L'') : PadicAlgCl q) = ((Φ x : L) : PadicAlgCl q)) :
    ∃ (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K₀)
      (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L)ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)
      (θ'' : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L'')ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
      (u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L)ˣ))
      (u'' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L'')ˣ)),
      ExtCitation.LocalLevel.IsBase q L (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) K₀ ∧
      ExtCitation.LocalLevel.IsBase q L'' (↥(NumberField.PlaceDecomp.decomp E M W)) K₀ ∧
      (∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : ((W.under (𝓞 F)).adicCompletion F)ˣ) : (W.under (𝓞 F)).adicCompletion F) = Φ.symm (y : L)) ∧
      (∀ y : (↥L'')ˣ, ((Additive.toMul (θ''.hom (Additive.ofMul y)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) = Φ''.symm (y : L'')) ∧
      ExtCitation.LocalLevel.IsLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) K₀ u ∧
      ExtCitation.LocalLevel.IsLocalFundamentalClass q L'' (↥(NumberField.PlaceDecomp.decomp E M W)) K₀ u'' ∧
      (groupCohomology.map r iD 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) θ 2).hom u) =
        Nat.card ↥r.ker • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M W)) θ'' 2).hom u'' ∧
      Nat.card ↥(NumberField.PlaceDecomp.decomp E M W) = Nat.card ↥r.ker * Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower.solution
