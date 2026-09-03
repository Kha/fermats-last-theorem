import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [CommRing k]
    (φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* k)
    (h : GeometricallyConnected (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ)))) :
    GeometricallyConnected
      (pullback.snd
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo.solution
