import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral
attribute [-instance] instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom
attribute [-simp] IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg
attribute [-simp] RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false
open Matrix MeasureTheory
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing NumberField.TateGlobal
open AutomorphicForm AdelicDock

attribute [local instance] NumberField.Idele.ideleBorel in

theorem
UnramifiedWhittaker.integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral
    (K : Type) [Field K] [NumberField K]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : S ⊆ T)
    (L : List (HeightOneSpectrum (𝓞 K))) (hL : L.Nodup) (hLT : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ L ↔ v ∈ T ∧ v ∉ S)
    (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 K),
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ≠ 0)
    (hϖ : ∀ v ∈ L, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (lam om : HeightOneSpectrum (𝓞 K) → ℂ)
    {I : HeightOneSpectrum (𝓞 K) → Type} [hIf : ∀ v, Fintype (I v)] [hIn : ∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 K), I v → v.adicCompletionIntegers K)
    (hN : ∀ v ∈ L, ∀ (y : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent y) * g) = StandardAddChar.psiLocal K v y * W g)
    (hK : ∀ v ∈ L, ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hU : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
      (u : AdeleRing (𝓞 K) K).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 K) K).2 v = 1) →
      finitePartUnits (𝓞 K) K u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), W (g * diagOne u) = W g)
    (hT : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b v i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        om v * W g)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
    (x : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    [hM : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [hB : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
    [hμ : ∀ v : HeightOneSpectrum (𝓞 K), (μ v).IsAddHaarMeasure]
    (hTint : Integrable
      (zetaIntegrand (fun g => W (g * (L.map fun v => placeEmbed K v (unipotent (x v))).prod)) χ s)
      (NumberField.Idele.productMeasureData K T).νS)
    (hSint : Integrable
      (zetaIntegrand
        (fun g => W (diagOne ((L.map fun v =>
            Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))
              ^ (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)))).prod) * g)) χ s)
      (NumberField.Idele.productMeasureData K S).νS)
    (hsum : ∀ v ∈ L, Summable fun m : ℤ =>
      ‖torusFactor (Fintype.card (I v)) (lam v) (om v)
          (m + LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v))
        * ((((χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 - s)) ^ m)
        * ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
                StandardAddChar.psiLocal K v
                    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ m * x v * u)
                  * LanglandsTunnell.TateLocal.charExt (localChar χ v) u ∂(μ v))
              / (((μ v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ))‖) :
    (∫ a, zetaIntegrand (fun g => W (g * (L.map fun v => placeEmbed K v (unipotent (x v))).prod)) χ s a
        ∂(NumberField.Idele.productMeasureData K T).νS)
      = (∫ a,
          zetaIntegrand
            (fun g => W (diagOne ((L.map fun v =>
                Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))
                  ^ (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)))).prod) * g)) χ s a
            ∂(NumberField.Idele.productMeasureData K S).νS)
        * (L.map fun v => ∑' m : ℤ,
            torusFactor (Fintype.card (I v)) (lam v) (om v)
                (m + LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v))
              * ((((χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 - s)) ^ m)
              * ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
                      StandardAddChar.psiLocal K v
                          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ m * x v * u)
                        * LanglandsTunnell.TateLocal.charExt (localChar χ v) u ∂(μ v))
                    / (((μ v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ))).prod := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral.solution
