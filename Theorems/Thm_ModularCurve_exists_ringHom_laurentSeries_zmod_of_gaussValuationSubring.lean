import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring

open ModularCurve

theorem ModularCurve.exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring
    (p : ℕ) [Fact p.Prime] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (W : ValuationSubring ↥F₀)
    (hW : ∀ f : ↥F₀, f ∈ W ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x) :
    ∃ red : ↥W →+* LaurentSeries (ZMod p),
      (∀ f : ↥W, red f = 0 ↔ (f : ↥F₀) ∈ W.nonunits) ∧
      ∀ (f : ↥W) (x y : LaurentSeries ℤ), coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 →
        ((f : ↥F₀) : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y =
          coeffMap (Int.castRingHom ℚ) x →
        red f * coeffMap (Int.castRingHom (ZMod p)) y = coeffMap (Int.castRingHom (ZMod p)) x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring.solution
