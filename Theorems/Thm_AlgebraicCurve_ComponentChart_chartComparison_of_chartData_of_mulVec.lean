import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_chartComparison_of_chartData_of_mulVec
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single
attribute [-simp] ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.chartComparison_of_chartData_of_mulVec
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] [HasPrincipalDivisors (AlgebraicClosure ℚ) F]
    {A : ValuationSubring (AlgebraicClosure ℚ)} (p : ℕ) (hp : p.Prime)
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {r : ℕ} (s t : Fin r → F) (hs0 : ∀ i, s i ≠ 0)

    (hint : ∀ i, t i ∈ C.integers)
    (cQ iQ : Place (ResidueField A) Fbar → Fin r)
    (hrat : ∀ P ∈ C.dom, P.IsRational ∧ (C.placeMap P).IsRational)
    (hcQ : ∀ P ∈ C.dom, C.residue ⟨t (cQ (C.placeMap P)), hint _⟩ ≠ 0)
    (hratio : ∀ P ∈ C.dom, ∀ j, t j * (t (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
    (hreg : ∀ P ∈ C.dom, ∀ j, t j * (t (cQ (C.placeMap P)))⁻¹ ∈ P.toValuationSubring)
    (himm : ∀ P ∈ C.dom, ∀ hmem : t (iQ (C.placeMap P)) * (t (cQ (C.placeMap P)))⁻¹ ∈ C.integers,
      (C.placeMap P).ord (C.residue ⟨_, hmem⟩
        - algebraMap (ResidueField A) Fbar ((C.placeMap P).evalAt (C.residue ⟨_, hmem⟩))) = 1)
    (hsep : ∀ P ∈ C.dom, ∀ Q ∈ C.dom, C.placeMap P ≠ C.placeMap Q →
      ∀ (hmP : ∀ j, t j * (t (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
        (hmQ : ∀ j, t j * (t (cQ (C.placeMap Q)))⁻¹ ∈ C.integers),
      ∃ i j, (C.placeMap P).evalAt (C.residue ⟨_, hmP i⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ j⟩)
        ≠ (C.placeMap P).evalAt (C.residue ⟨_, hmP j⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ i⟩))

    (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (hM : Minv * M = 1) (B : ℕ)
    (hMB : ∀ i j, (p : AlgebraicClosure ℚ) ^ B * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ B * Minv i j ∈ A)
    (hlink : ∀ P ∈ C.dom, ∃ d : AlgebraicClosure ℚ, d ≠ 0 ∧
      evalVec s P = d • M.mulVec (fun i => P.evalAt (t i * (t (cQ (C.placeMap P)))⁻¹)))

    (T : Place (ResidueField A) Fbar → F)
    (hT : ∀ P ∈ C.dom,
      ∃ h : T (C.placeMap P) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T (C.placeMap P))) ∈ C.integers,
        C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap P).ord (C.residue ⟨_, h⟩) = 1 ∧
        0 < P.ord (T (C.placeMap P) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T (C.placeMap P)))) ∧
        ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P → Q ≠ P →
          Q.ord (T (C.placeMap P) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T (C.placeMap P)))) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ C.dom, ∀ Q ∈ C.dom, P ≠ Q →
        (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
        ((C.placeMap P = C.placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)
              + Real.log (μ (P.evalAt (T (C.placeMap P)) - Q.evalAt (T (C.placeMap P))))|
            ≤ (4 * B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (C.placeMap P ≠ C.placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ (4 * B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_chartComparison_of_chartData_of_mulVec.solution
