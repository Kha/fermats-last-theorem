import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_iso_pullback_igusaTo_rat_twoChartIntegralModel_and_iotaFin

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme AlgebraicCurve

theorem ModularCurve.IgusaScheme.exists_iso_pullback_igusaTo_rat_twoChartIntegralModel_and_iotaFin
    (N q : ℕ) [NeZero N] [Fact q.Prime] :
    ∃ (ε : pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ))) ≅
        TwoChartIntegralModel ℚ ↥(modularFunctionFieldFull N) (jFull N))
      (κ : pullback (ιFin N q)
          (pullback.fst (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))) ≅
        Spec (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℚ ↥(modularFunctionFieldFull N) (jFull N))))
      (θ : ↥(IgusaScheme.chartAlgFin N q) →ₐ[↥(GaloisRep.ratLocalizedAt q)]
        ↥(TwoChartIntegralModel.chartAlgFin ℚ ↥(modularFunctionFieldFull N) (jFull N))),

      ε.hom ≫ TwoChartIntegralModel.toBase ℚ ↥(modularFunctionFieldFull N) (jFull N) = pullback.snd _ _ ∧

      pullback.snd (ιFin N q)
          (pullback.fst (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))) ≫ ε.hom =
        κ.hom ≫ TwoChartIntegralModel.ιFin ℚ ↥(modularFunctionFieldFull N) (jFull N) ∧

      (∀ x, (θ x : ↥(modularFunctionFieldFull N)) = x) ∧
      κ.hom ≫ Spec.map (CommRingCat.ofHom θ.toRingHom) =
        pullback.fst (ιFin N q)
          (pullback.fst (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_iso_pullback_igusaTo_rat_twoChartIntegralModel_and_iotaFin.solution
