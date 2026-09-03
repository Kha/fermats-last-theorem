import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Algebra.MvPolynomial.Eval
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_exists_symmValue_rows_kernel_iff
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk
attribute [-simp] ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen
attribute [-simp] ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.Divisor.exists_symmValue_rows_kernel_iff
    {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]
    {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F] [CharZero k]
    (hfin : ∀ x : F, x ≠ 0 → {v : Place k F | x ∉ v.toValuationSubring}.Finite)
    (hrat : ∀ (v : Place k F) (x : F), j ∈ v.toValuationSubring →
      IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ c : k, x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'')
    (q₀ : Polynomial K₀) (v₀ : Place k F) (g e mdeg : ℕ) :
    ∃ (Θ : Polynomial K₀) (a : ℕ) (cL₀ : Fin a → Polynomial K₀) (cL : Fin a → Fin n → Polynomial K₀)
      (χ : Fin a → Polynomial (Polynomial K₀))
      (M : ℕ) (Rm : Fin M → ℕ) (Y : (l : Fin M) → Fin (Rm l) → Fin n × Fin (mdeg + 1) → k)
      (R : Fin (g + 1) → ℕ)
      (P : (r : Fin (g + 1)) → Fin (R r) → Fin n × Fin (mdeg + 1) →
        MvPolynomial (Fin (a + 1) × Fin ((r : ℕ) + 1)) K₀),
      (∀ s, (χ s).Monic) ∧
      ∀ (D : Divisor k F), (∀ v, 0 ≤ D v) → Divisor.degree D = (g : ℤ) →
        ∃ (r : Fin (g + 1)) (l : Fin M) (pt : Fin (r : ℕ) → Place k F)
          (val : Fin (r : ℕ) × Fin (a + 1) → k)
          (r' : ℕ) (pt' : Fin r' → Place k F) (jv' : Fin r' → k),
          (∀ t, 0 ≤ (pt t).ord j ∧
            (pt t).ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) = 0) ∧
          (∀ t', 0 < (pt' t').ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k)))) ∧
          (∀ v : Place k F, 0 ≤ v.ord j → D v =
            ((∑ t, Finsupp.single (pt t) (1 : ℤ))
              + ∑ t', Finsupp.single (pt' t') (1 : ℤ) : Divisor k F) v) ∧
          (∀ t, 0 < (pt t).ord (j - algebraMap k F (val (t, 0)))) ∧
          (∀ t (s : Fin a), 0 < (pt t).ord
            ((Polynomial.aeval j ((cL₀ s).map (algebraMap K₀ k))
              + ∑ i : Fin n, Polynomial.aeval j ((cL s i).map (algebraMap K₀ k)) * b i)
              - algebraMap k F (val (t, s.succ)))) ∧
          (∀ t', 0 < (pt' t').ord (j - algebraMap k F (jv' t'))) ∧
          (∀ t (s : Fin a), Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ k) (val (t, 0)))
              (val (t, s.succ)) (χ s) = 0) ∧
          ∀ u : Fin n × Fin (mdeg + 1) → k,
            ((∀ ρ : Fin (R r), ∑ col, MvPolynomial.aeval
                  (fun ak : Fin (a + 1) × Fin ((r : ℕ) + 1) =>
                    (∏ t : Fin (r : ℕ), (Polynomial.X - Polynomial.C (val (t, ak.1)))).coeff ak.2)
                  (P r ρ col) * u col = 0) ∧
              (∀ ρ : Fin (Rm l), ∑ col, Y l ρ col * u col = 0)) ↔
            (u = 0 ∨ ∀ v : Place k F,
              0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
                + v.ord ((∑ i : Fin n, Polynomial.aeval j
                      (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
                    * (Polynomial.aeval j
                        ((∏ t : Fin (r : ℕ), (Polynomial.X - Polynomial.C (val (t, 0))))
                          * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
                          * q₀.map (algebraMap K₀ k)))⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_exists_symmValue_rows_kernel_iff.solution
