import Mathlib
import Definitions.Def_ModularCurve_UVCrossingInitialForm
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (hgood0 : ∃ i, IsUnit (PowerSeries.coeff i ab.1))
    (hgoodE : IsUnit (PowerSeries.constantCoeff ab.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab.2))
    [Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})]
    [Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})]
    (hΔ : (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) : ℤ) =
      sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)) :
    leadingResidue ϖ (((LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e)))).charpoly).coeff 0) *
        leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) =
      leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf.solution
