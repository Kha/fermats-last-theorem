import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_ChordalProximity
import P2M.Util
import P2M.Sol.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single
attribute [-simp] ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.annulusComparison_of_attached_at_both_ends_of_certifiedFamily (N : ℕ) [NeZero N]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
    ∀ (k₀ : ℕ) (t : Fin r → modularFunctionFieldBar N)
      (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (nexp : Fin r → ℕ) (Bl : ℕ),
    (∀ l : Fin r, (l : ℕ) = 0 → t l = 1) →
    (∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (M i j) * t j) →
    Minv * M = 1 → M * Minv = 1 →
    (∀ l : Fin r, (l : ℕ) = 0 → nexp l = 0) → (∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ nexp l) →
    (∀ l, nexp l ≤ k₀) →
    ∃ (Cc : ℝ), ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ {Fbar Fbar' : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
      [Field Fbar'] [Algebra (ResidueField ↥A) Fbar']
      (C : ComponentChart A (modularFunctionFieldBar N) Fbar)
      (C' : ComponentChart A (modularFunctionFieldBar N) Fbar')
      (x : Place (ResidueField ↥A) Fbar) (x' : Place (ResidueField ↥A) Fbar')
      (An An' : Annulus A (modularFunctionFieldBar N)),
    An.IsAttached C x → An'.IsAttached C' x' →
    (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      ((An.modulus : AlgebraicClosure ℚ)) ≠ 0 ∧
      An'.param * An.param
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An.modulus : AlgebraicClosure ℚ))) →
    ∀ (πx : AlgebraicClosure ℚ), πx ≠ 0 → (∃ hmem : πx ∈ A, (⟨πx, hmem⟩ : A) ∈ maximalIdeal A) →
    (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
      ((An.modulus : AlgebraicClosure ℚ)) * u = πx) →
    (∃ a : AlgebraicClosure ℚ, a ∈ A ∧ (p : AlgebraicClosure ℚ) ^ k₀ = πx * a) →
    (∃ b : AlgebraicClosure ℚ, b ∈ A ∧ πx = (p : AlgebraicClosure ℚ) * b) →

    ∀ (U Uinv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (f : Fin r → modularFunctionFieldBar N),
    (∀ i j, U i j ∈ A ∧ Uinv i j ∈ A) → Uinv * U = 1 ∧ U * Uinv = 1 →
    (∀ l, f l = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (U l j) * t j) →

    ∀ (w : ℕ), 2 ≤ w →
    (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
      ((An.modulus : AlgebraicClosure ℚ)) = (p : AlgebraicClosure ℚ) ^ w * u) →

    (∃ hint : ∀ l : Fin r, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * f l ∈ C.integers,
      (∀ l : Fin r, C.residue ⟨_, hint l⟩ ≠ 0) ∧
      (∀ l : Fin r, x.ord (C.residue ⟨_, hint l⟩) = -((nexp l / w : ℕ) : ℤ)) ∧
      LinearIndependent (ResidueField ↥A) (fun l => C.residue ⟨_, hint l⟩)) →

    (∀ i j, (p : AlgebraicClosure ℚ) ^ Bl * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ Bl * Minv i j ∈ A) →

    (∀ l : Fin r, ∃ h : f l ∈ C'.integers,
      C'.residue ⟨f l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ x'.ord (C'.residue ⟨f l, h⟩))) →
    (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : f l ∈ C'.integers, x'.ord (C'.residue ⟨f l, h⟩) = 1) →

    (∀ l : Fin r, (l : ℕ) = 0 → f l = 1) →
    (∀ R ∈ An.dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
      f l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (f l) ∈ A, (⟨R.evalAt (f l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) →

    ((∃ l : Fin r, 1 ≤ (l : ℕ) ∧ (∃ h : f l ∈ C'.integers, x'.ord (C'.residue ⟨f l, h⟩) = 1) ∧ nexp l = w) ∨
     (∃ m₁ m₂ : Fin r, 1 ≤ (m₁ : ℕ) ∧ 1 ≤ (m₂ : ℕ) ∧
        (∃ h : f m₁ ∈ C'.integers, x'.ord (C'.residue ⟨f m₁, h⟩) = 1) ∧
        (∃ h : f m₂ ∈ C'.integers, x'.ord (C'.residue ⟨f m₂, h⟩) = 1) ∧
        nexp m₁ < nexp m₂ ∧ nexp m₂ < w ∧ nexp m₁ + w ≤ 2 * nexp m₂ ∧
        (∃ (h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              ((p : AlgebraicClosure ℚ) ^ nexp m₁))⁻¹ * f m₁ ∈ C.integers) (c : ResidueField ↥A),
          x.ord (C.residue ⟨_, h⟩ - algebraMap (ResidueField ↥A) Fbar c) = 1))) →

    (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ An.dom, ∀ Q ∈ An.dom, P ≠ Q →
        (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
        |prox μ (evalVec s P) (evalVec s Q)
            + Real.log (μ (P.evalAt An.param - Q.evalAt An.param))|
          ≤ Cc * (-Real.log (μ ((An.modulus : AlgebraicClosure ℚ))))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily.solution
