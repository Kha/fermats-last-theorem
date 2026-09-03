import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_inv_sub_pos
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_laurentDescent_apply ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply
attribute [-simp] ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
attribute [-simp] AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec

set_option autoImplicit false
open AlgebraicCurve ModularCurve.CharPModel in
theorem ModularCurve.twoComponentExhaustion_valuation_mul_lt_one_of_ord_inv_sub_pos
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓA : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1) (hlN : ¬ ℓ ∣ N)
    (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ))
    (hσ : IsAtkinLehnerAutFull N ℓ σ)
    (W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))
    (c₁ : A)
    (hj₁ : 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (N * ℓ) (jq_mem (N * ℓ)))⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))⁻¹
      - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
        (c₁ : AlgebraicClosure ℚ)))
    (c₂ : A)
    (hj₂ : 0 < W.ord ((heckeBetaBar (AlgebraicClosure ℚ) N ℓ
        ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩)⁻¹
      - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
        (c₂ : AlgebraicClosure ℚ)))
    (e f : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
    (he : ∃ p : Polynomial (Subring.closure (Set.range (constantsHom (N * ℓ) A) ∪
            {((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full (N * ℓ) (jq_mem (N * ℓ)))⟩ :
                laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))⁻¹,
              (heckeBetaBar (AlgebraicClosure ℚ) N ℓ
                ⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                    (modularFunctionField_le_full N (jq_mem N))⟩)⁻¹})), p.Monic ∧
      Polynomial.eval₂ (Subring.closure (Set.range (constantsHom (N * ℓ) A) ∪
            {((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full (N * ℓ) (jq_mem (N * ℓ)))⟩ :
                laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))⁻¹,
              (heckeBetaBar (AlgebraicClosure ℚ) N ℓ
                ⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                    (modularFunctionField_le_full N (jq_mem N))⟩)⁻¹})).subtype e p = 0)
    (hf : ∃ p : Polynomial (Subring.closure (Set.range (constantsHom (N * ℓ) A) ∪
            {((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full (N * ℓ) (jq_mem (N * ℓ)))⟩ :
                laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))⁻¹,
              (heckeBetaBar (AlgebraicClosure ℚ) N ℓ
                ⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                    (modularFunctionField_le_full N (jq_mem N))⟩)⁻¹})), p.Monic ∧
      Polynomial.eval₂ (Subring.closure (Set.range (constantsHom (N * ℓ) A) ∪
            {((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full (N * ℓ) (jq_mem (N * ℓ)))⟩ :
                laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))⁻¹,
              (heckeBetaBar (AlgebraicClosure ℚ) N ℓ
                ⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                    (modularFunctionField_le_full N (jq_mem N))⟩)⁻¹})).subtype f p = 0)
    (a b : A)
    (hea : 0 < W.ord (e - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
      (a : AlgebraicClosure ℚ)))
    (hfb : 0 < W.ord (f - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
      (b : AlgebraicClosure ℚ)))
    (heInf : ∀ n : ℤ,
      A.valuation ((e : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1)
    (hfZero : ∀ n : ℤ,
      A.valuation (((geomAut (AlgebraicClosure ℚ) _ σ) f : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1) :
    A.valuation ((a : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ)) < 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_inv_sub_pos.solution
