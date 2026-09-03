import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open AlgebraicCurve

theorem ModularCurve.CharPModel.FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))).Separable)
    (R : AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar N)
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N))
    (hspec : ∀ (y : LaurentSeries A) (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar N),
      ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ : ModularCurve.modularFunctionFieldBar N) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) = ModularCurve.coeffMap (IsLocalRing.residue A) y)
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N))
    (hP : ∃ a : A, ModularCurve.CharPModel.jBar N -
        algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits)
    (Q : AlgebraicCurve.Place (IsLocalRing.ResidueField A)
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N))
    (hclause : ∀ h : R.integers,
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
          ({ModularCurve.CharPModel.jBar N} : Set (ModularCurve.modularFunctionFieldBar N)))
        (h : ModularCurve.modularFunctionFieldBar N) →
      ∀ a : A, (h : ModularCurve.modularFunctionFieldBar N) -
          algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits →
        R.residue h - algebraMap (IsLocalRing.ResidueField A)
            (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N) (IsLocalRing.residue A a) ∈
          Q.toValuationSubring.nonunits) :
    fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P = Q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.solution
