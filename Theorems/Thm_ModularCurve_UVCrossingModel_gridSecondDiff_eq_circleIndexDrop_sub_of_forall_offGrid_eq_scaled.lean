import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled
set_option autoImplicit false
open ModularCurve ModularCurve.UVCrossingModel IsLocalRing
universe u

theorem ModularCurve.UVCrossingModel.gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (ew eK : ℕ) (hew : 1 ≤ ew) (heK : 1 ≤ eK) (e : ℕ) (he : e = ew * eK)
    (e' : ℕ) (he' : 1 ≤ e')
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (x' : UVCrossingModel W (ϖ ^ e)) (hx' : x' ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (habx' : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = x')
    (hagree : ∀ r s : ℕ, 1 ≤ r → 0 < s → s < r * (e' * e) → (¬ ∃ d, d ≤ e' * ew ∧ s = r * (e' * e - d * eK)) →
        circleIndexDrop (fun w => ((r * e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * e' * e) s ab =
          circleIndexDrop (fun w => ((r * e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * e' * e) s ab')
    (φ : ℕ → ℤ)
    (hφ : ∀ t, φ t =
        ((gaussOrder (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (e' * e) t x).toNat : ℤ)
        - (gaussOrder (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (e' * e) t x').toNat)
    (G : ℕ → ℤ) (hG : ∀ d, G d = (φ (e' * e - d * eK) - φ (e' * e)) / eK) :
    (∀ d, d ≤ e' * ew → (eK : ℤ) ∣ φ (e' * e - d * eK) - φ (e' * e)) ∧
    (∀ d ∈ Finset.Ico 1 (e' * ew), (G d - G (d - 1)) - (G (d + 1) - G d) =
        (circleIndexDrop (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e)
            (e' * e - d * eK) ab : ℤ)
          - circleIndexDrop (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e)
            (e' * e - d * eK) ab') ∧
    G 1 - G 0 =
      -((sSup (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w)
            (e' * e) (e' * e) ab) : ℤ)
        - sSup (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w)
            (e' * e) (e' * e) ab')) ∧
    G (e' * ew) - G (e' * ew - 1) =
      -((sInf (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e) 0 ab) : ℤ)
        - sInf (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e) 0 ab')) ∧
    G 1 - G 0 = -(φ (e' * e) - φ (e' * e - 1)) ∧ G (e' * ew) - G (e' * ew - 1) = -(φ 1 - φ 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled.solution
