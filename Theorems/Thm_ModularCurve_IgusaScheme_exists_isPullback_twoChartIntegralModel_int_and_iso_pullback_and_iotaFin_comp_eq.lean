import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.IgusaScheme.exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ v : IgusaScheme N ℓ ⟶
        AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull N) (jFull N),
      IsPullback v (igusaTo N ℓ)
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ∧
      (∀ (S : Type) [CommRing S] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) S],
        ∃ I : pullback (igusaTo N ℓ)
              (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S))) ≅
            pullback
              (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
              (Spec.map (CommRingCat.ofHom (algebraMap ℤ S))),
          I.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
          I.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ v) ∧
      ιFin N ℓ ≫ v =
        Spec.map (CommRingCat.ofHom
          (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange ℤ ↥(modularFunctionFieldFull N) ↥(GaloisRep.ratLocalizedAt ℓ) {jFull N})) ≫
          AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull N) (jFull N) ∧
      ιInf N ℓ ≫ v =
        Spec.map (CommRingCat.ofHom
          (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange ℤ ↥(modularFunctionFieldFull N) ↥(GaloisRep.ratLocalizedAt ℓ) {(jFull N)⁻¹})) ≫
          AlgebraicCurve.TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull N) (jFull N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq.solution
