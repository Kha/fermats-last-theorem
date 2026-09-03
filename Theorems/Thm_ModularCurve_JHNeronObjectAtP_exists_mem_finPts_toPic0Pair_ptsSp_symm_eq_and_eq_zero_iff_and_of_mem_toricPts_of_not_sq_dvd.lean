import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_exists_mem_finPts_toPic0Pair_ptsSp_symm_eq_and_eq_zero_iff_and_of_mem_toricPts_of_not_sq_dvd
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing
open ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.exists_mem_finPts_toPic0Pair_ptsSp_symm_eq_and_eq_zero_iff_and_of_mem_toricPts_of_not_sq_dvd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (n : ℕ) (hn : 0 < n) :
    (∀ b : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
        (p ^ n) • b = 0 →
        ∃ x ∈ O.finPts (p ^ n), ∃ (s : SchemeHomOver Λ.σA O.g) (_ : (O.pts x).1 = barPt A ≫ s.1)
          (sκ : SchemeHomOver (resPt A ≫ Λ.σA) O.g) (_ : sκ.1 = resPt A ≫ s.1),
          GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm sκ) = b) ∧
    (∀ x ∈ O.finPts (p ^ n), ∀ (s : SchemeHomOver Λ.σA O.g), (O.pts x).1 = barPt A ≫ s.1 →
      ∀ (sκ : SchemeHomOver (resPt A ≫ Λ.σA) O.g), sκ.1 = resPt A ≫ s.1 →
        (GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm sκ) = 0 ↔ O.ptsSp.symm sκ = 0)) ∧

    (∀ x ∈ O.toricPts (p ^ n), ∀ (s : SchemeHomOver Λ.σA O.g), (O.pts x).1 = barPt A ≫ s.1 →
      ∀ (sκ : SchemeHomOver (resPt A ≫ Λ.σA) O.g), sκ.1 = resPt A ≫ s.1 → O.ptsSp.symm sκ = 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_mem_finPts_toPic0Pair_ptsSp_symm_eq_and_eq_zero_iff_and_of_mem_toricPts_of_not_sq_dvd.solution
