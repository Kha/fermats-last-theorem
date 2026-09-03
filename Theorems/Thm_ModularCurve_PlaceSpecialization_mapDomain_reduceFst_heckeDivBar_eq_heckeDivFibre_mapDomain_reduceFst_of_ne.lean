import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne
    (N q : ℕ) [NeZero N] (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R₁ : RegularProlongation A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField A) N))
      (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ V, D V = V.ord (f : modularFunctionFieldBar N)) →
        ∀ Q, Finsupp.mapDomain P.sp D Q = Q.ord (R₁.residue f)),
        ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q →
          ∀ [Fact (ℓ : ℕ).Prime]
            (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
            (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
            (hαc : HeckeAlphaCIntegral (ResidueField A) N ℓ)
            (hβc : HeckeBetaCIntegral (ResidueField A) N ℓ)
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * (ℓ : ℕ)))]
            [HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ)]
            (hdeg1 : ∀ Y : Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ), Y.deg = 1)
            (Rℓ : RegularProlongation A (modularFunctionFieldBar (N * (ℓ : ℕ)))
              (charLDegeneracyRoof (ResidueField A) N ℓ))
            (rℓ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * (ℓ : ℕ)))
              → Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ))
            (hrℓ : ∀ f : Rℓ.integers, Rℓ.residue f ≠ 0 →
              ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * (ℓ : ℕ))),
                (∀ V, D V = V.ord (f : modularFunctionFieldBar (N * (ℓ : ℕ)))) →
              ∀ Q, Finsupp.mapDomain rℓ D Q = Q.ord (Rℓ.residue f))
            (hRα : ∀ f : R₁.integers,
              ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N) ∈ Rℓ.integers,
                Rℓ.residue ⟨_, h⟩ = heckeAlphaC (ResidueField A) N ℓ (R₁.residue f))
            (hRβ : ∀ f : R₁.integers,
              ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N) ∈ Rℓ.integers,
                Rℓ.residue ⟨_, h⟩ = heckeBetaC (ResidueField A) N ℓ (R₁.residue f))
            (hdegα : ∀ v, Divisor.degree
                (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ (Finsupp.single v 1))
              = Divisor.degree (Divisor.pullbackAlong (heckeAlphaC (ResidueField A) N ℓ) hαc
                  (Finsupp.single (P.sp v) 1)))
            (hdegβ : ∀ v, Divisor.degree
                (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ (Finsupp.single v 1))
              = Divisor.degree (Divisor.pullbackAlong (heckeBetaC (ResidueField A) N ℓ) hβc
                  (Finsupp.single (P.sp v) 1)))
          (hαq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
          (hβq : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q * (ℓ : ℕ)))]
          (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          Finsupp.mapDomain P.reduceFst (heckeDivBar hαq hβq X) =
            heckeDivFibre (ResidueField A) N ℓ hβc hαc (Finsupp.mapDomain P.reduceFst X) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne.solution
