import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import P2M.Util
import P2M.Sol.S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]
    (K : IntermediateField L (LaurentSeries L)) [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)] :
    ∃ (w : ModularCurve.TwoChartModel A (↥K) j ≅ AlgebraicCurve.TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) (↥K) j)
      (eFin : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j))
      (eInf : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) ≃+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j)),

      (∀ x : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        ((eFin x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j)) : ↥K) = (x : ↥K)) ∧
      (∀ x : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
        ((eInf x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j)) : ↥K) = (x : ↥K)) ∧

      w.hom ≫ AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) (↥K) j =
        ModularCurve.TwoChart.modelTo A (↥K) j ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)) ∧

      ModularCurve.TwoChart.ιFin A (↥K) j ≫ w.hom =
        Spec.map (CommRingCat.ofHom eFin.symm.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j ∧
      ModularCurve.TwoChart.ιInf A (↥K) j ≫ w.hom =
        Spec.map (CommRingCat.ofHom eInf.symm.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j ∧

      w.hom ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange ∧
      w.hom ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j).opensRange = (ModularCurve.TwoChart.ιInf A (↥K) j).opensRange := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension.solution
