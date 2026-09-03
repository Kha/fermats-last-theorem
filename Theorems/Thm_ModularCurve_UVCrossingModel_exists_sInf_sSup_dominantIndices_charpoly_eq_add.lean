import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.exists_sInf_sSup_dominantIndices_charpoly_eq_add
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    [Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})]
    [Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})]
    (hΔ : (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) : ℤ) =
      sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)) :
    ∃ n₀ : ℤ, ∀ q : ℕ, 1 ≤ q →
      (∀ p : ℕ, p + 1 ≤ q * e →
        sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p
            (((LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e)))).charpoly : PowerSeries W), 0)) =
          sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) + n₀) ∧
      (∀ p : ℕ, 1 ≤ p → p ≤ q * e →
        sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p
            (((LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e)))).charpoly : PowerSeries W), 0)) =
          sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) + n₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.solution
