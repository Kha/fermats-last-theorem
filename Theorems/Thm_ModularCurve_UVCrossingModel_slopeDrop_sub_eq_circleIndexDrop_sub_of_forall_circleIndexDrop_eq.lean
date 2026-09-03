import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (x' : UVCrossingModel W (ϖ ^ e)) (hx' : x' ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (habx' : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = x')
    (hoff : ∀ r s : ℕ, 1 ≤ r → ¬ r ∣ s → 0 < s → s < r * q * e →
        circleIndexDrop (fun w => ((r * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * q * e) s ab =
          circleIndexDrop (fun w => ((r * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * q * e) s ab') :
    (∀ p : ℕ, 1 ≤ p → p + 1 ≤ q * e →
      ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x').toNat)
        - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x').toNat))
      - ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x').toNat)
        - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x').toNat))
      = (circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab : ℤ)
        - circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab') ∧
    ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 1 x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 1 x').toNat)
      - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 0 x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 0 x').toNat)
      = sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab)
        - sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab')) ∧
    ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e) x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e) x').toNat)
      - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e - 1) x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e - 1) x').toNat)
      = sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) ab)
        - sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) ab')) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq.solution
