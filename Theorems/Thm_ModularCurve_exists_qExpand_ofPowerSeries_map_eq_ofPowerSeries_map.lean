import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_qExpand_ofPowerSeries_map_eq_ofPowerSeries_map

set_option autoImplicit false

theorem ModularCurve.exists_qExpand_ofPowerSeries_map_eq_ofPowerSeries_map
    (A : Type*) [CommRing A] (L : Type*) [Field L] [Algebra A L] (N : ℕ) [NeZero N] (x : PowerSeries A) :
    ∃ x' : PowerSeries A,
      (∀ n : ℕ, PowerSeries.coeff n x' = if N ∣ n then PowerSeries.coeff (n / N) x else 0) ∧
      ModularCurve.qExpand L N (HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) =
        HahnSeries.ofPowerSeries ℤ L (x'.map (algebraMap A L)) ∧
      ∀ (B : Type*) [CommRing B] (φ : A →+* B), x'.map φ = 0 ↔ x.map φ = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_qExpand_ofPowerSeries_map_eq_ofPowerSeries_map.solution
