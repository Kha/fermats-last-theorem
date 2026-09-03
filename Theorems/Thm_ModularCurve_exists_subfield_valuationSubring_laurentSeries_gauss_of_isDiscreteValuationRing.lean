import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing

theorem ModularCurve.exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing
    (L : Type) [Field L] (A₀ : ValuationSubring L) (hdvr : IsDiscreteValuationRing ↥A₀) :
    ∃ (L₂ : Subfield (LaurentSeries L)) (W₂ : ValuationSubring ↥L₂),

      (∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
        f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) ∧

      (∀ f : ↥L₂, f ∈ W₂ ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
        ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) ∧

      (∀ f : ↥L₂, f ∈ W₂.nonunits ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
        x.map (IsLocalRing.residue ↥A₀) = 0 ∧
        ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing.solution
