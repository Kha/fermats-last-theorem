import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (y : UVCrossingModel W (ϖ ^ e)) (hy : y ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (haby : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = y)
    (ab'' : PowerSeries W × PowerSeries W) (hb'' : PowerSeries.constantCoeff ab''.2 = 0)
    (habxy : mk (ϖ ^ e) (inU ab''.1 + inV ab''.2) = x * y) :
    sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab'') =
        sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) +
          sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab') ∧
      sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab'') =
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) +
          sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul.solution
