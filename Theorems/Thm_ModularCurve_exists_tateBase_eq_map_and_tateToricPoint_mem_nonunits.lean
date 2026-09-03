import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits

theorem ModularCurve.exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits
    (L : Type) [Field L] (A₀ : ValuationSubring L)
    (L₂ : Subfield (LaurentSeries L)) (W₂ : ValuationSubring ↥L₂)
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (hW₂ : ∀ f : ↥L₂, f ∈ W₂ ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
      ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (hW₂' : ∀ f : ↥L₂, f ∈ W₂.nonunits ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
      x.map (IsLocalRing.residue ↥A₀) = 0 ∧
      ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (p : ℕ) [NeZero p] (c : (↥A₀)ˣ) (hc : 1 - (c : ↥A₀) ∈ IsLocalRing.maximalIdeal ↥A₀) (hc1 : ((c : ↥A₀) : L) ≠ 1) :

    (∃ T : WeierstrassCurve ↥W₂,
      (T.map W₂.subtype).map L₂.subtype = ModularCurve.tateBase L p ∧
      (T.map (IsLocalRing.residue ↥W₂)).Δ ≠ 0) ∧

    (∃ xt yt : ↥L₂,
      ((xt : ↥L₂) : LaurentSeries L) = (ModularCurve.tateToricPoint L p (Units.map (A₀.subtype : ↥A₀ →* L) c)).1 ∧
      ((yt : ↥L₂) : LaurentSeries L) = (ModularCurve.tateToricPoint L p (Units.map (A₀.subtype : ↥A₀ →* L) c)).2 ∧
      yt ≠ 0 ∧ xt / yt ∈ W₂.nonunits ∧ yt⁻¹ ∈ W₂.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits.solution
