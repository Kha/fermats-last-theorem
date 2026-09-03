import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_isPullback_twoChartIntegralModel_int_and_iso_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.IgusaScheme.exists_isPullback_twoChartIntegralModel_int_and_iso_pullback
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ v : IgusaScheme N ℓ ⟶
        AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull N) (jFull N),
      IsPullback v (igusaTo N ℓ)
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ∧
      ∀ (S : Type) [CommRing S] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) S],
        ∃ I : pullback (igusaTo N ℓ)
              (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S))) ≅
            pullback
              (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
              (Spec.map (CommRingCat.ofHom (algebraMap ℤ S))),
          I.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
          I.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ v := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_isPullback_twoChartIntegralModel_int_and_iso_pullback.solution
