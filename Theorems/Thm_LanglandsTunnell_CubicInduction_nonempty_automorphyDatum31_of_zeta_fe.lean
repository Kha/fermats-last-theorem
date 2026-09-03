import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_nonempty_automorphyDatum31_of_zeta_fe
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff
attribute [-simp] RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.nonempty_automorphyDatum31_of_zeta_fe
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (_hψS : ∀ v ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (a : HeightOneSpectrum (𝓞 ℚ) → ℕ) (_ha : ∀ v ∈ S, 1 ≤ a v)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (_hωa : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v (2 * a v - 1), localChar ω v u = 1)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hWc : Continuous W)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (_hWK : ∀ v ∈ S, IsCongruenceEquivariantAlong v (a v) (localChar ω v) W)
    (_hWl : ∀ v ∈ S, HasVanishingUnipotentIntegralAlong v W)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (_hgrowth : IsModerateGrowth3 ℚ fun g => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g))
    (_hcont : Continuous fun g => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g))
    (_hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hcont' : Continuous fun g => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hint : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
        MeasureTheory.Integrable (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          ‖W (iotaGL (diagUnitGL2 x) * g)‖ * (TateGlobal.ideleNorm ℚ x : ℝ) ^ (σ - 1))
          (NumberField.Idele.idelicHaar ℚ))
    (_hint' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
        MeasureTheory.Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
          ‖dualWhittakerFn3 W
              (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 g))‖ *
            (TateGlobal.ideleNorm ℚ p.1 : ℝ) ^ (σ - 1))
          ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (_hinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) W)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) W (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) W (lam2 p))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (c : ℂ) (_hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1)
    (_hfe : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      ∀ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ → (∀ v ∈ S, IsUnramifiedCharAt χ v) →
        ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ LanglandsTunnell.LDatum.BoundedOnStrips E ∧ ∃ σ₁ σ₂ : ℝ,
          (∀ s : ℂ, σ₁ < s.re → E s = globalZeta30 W χ s g) ∧
          (∀ s : ℂ, s.re < σ₂ → E s = c * globalZetaDual31 W χ (1 - s) g)) :
    Nonempty (AutomorphyDatum31 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ S a ω W lam1 lam2) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_nonempty_automorphyDatum31_of_zeta_fe.solution
