import Definitions.Def_ModularCurve_JZeroNaiveHeight
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_height_system_modularFunctionFieldBar
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen
attribute [-simp] ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.exists_height_system_modularFunctionFieldBar (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' g'' : ℕ) (hle : g' ≤ g'') (n : ℕ) (b : Fin n → modularFunctionFieldBar N)
    (hbQ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (i : Fin n),
      arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • b i = b i)
    (hbli : ∀ c : Fin n → Polynomial (AlgebraicClosure ℚ),
      (∑ i : Fin n, Polynomial.aeval
          (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
            (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (c i) * b i) = 0
        → ∀ i, c i = 0)
    (hbsp : ∀ x : modularFunctionFieldBar N, ∃ (q : Polynomial (AlgebraicClosure ℚ))
        (c : Fin n → Polynomial (AlgebraicClosure ℚ)), q ≠ 0 ∧
        x * Polynomial.aeval
            (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
              (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) q
          = ∑ i : Fin n, Polynomial.aeval
              (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
                (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (c i) * b i) :
    ∃ (mdeg rdim qdeg : ℕ) (α β : ℝ), 0 ≤ α ∧
      ∀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))),
        (∀ v, 0 ≤ D v) →
        ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
            + (g'' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D) →
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
            arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D = D) →
        ∀ hmem : ∀ k, symVec N g'' D k ∈ K,
        ∃ qK : Polynomial K, qK ≠ 0 ∧ qK.natDegree ≤ qdeg ∧
        ∃ Msys : Matrix (Fin rdim) (Fin n × Fin (mdeg + 1)) K,
          Height.logHeight (fun ij : Fin rdim × (Fin n × Fin (mdeg + 1)) => Msys ij.1 ij.2)
            ≤ α * Height.logHeight (fun k : Fin (g'' + 1) => (⟨symVec N g'' D k, hmem k⟩ : K)) + β ∧
          (∀ u : Fin n × Fin (mdeg + 1) → AlgebraicClosure ℚ, u ≠ 0 →
            ((Msys.map (algebraMap K (AlgebraicClosure ℚ))).mulVec u = 0 ↔
              ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
                0 ≤ (D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1
                      : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) v
                  + v.ord ((∑ i : Fin n, Polynomial.aeval
                        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
                          (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
                        (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ))
                        * b i)
                      * (Polynomial.aeval
                          (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
                            (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
                          (qK.map (algebraMap K (AlgebraicClosure ℚ))))⁻¹))) ∧
          (∀ f : modularFunctionFieldBar N, f ≠ 0 →
            (∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
              0 ≤ (D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1
                    : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) v + v.ord f) →
            ∃ u : Fin n × Fin (mdeg + 1) → AlgebraicClosure ℚ, u ≠ 0 ∧
              (∑ i : Fin n, Polynomial.aeval
                  (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
                    (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
                  (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ))
                  * b i)
                * (Polynomial.aeval
                    (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
                      (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
                    (qK.map (algebraMap K (AlgebraicClosure ℚ))))⁻¹ = f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_height_system_modularFunctionFieldBar.solution
