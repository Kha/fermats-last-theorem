import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_tateToricPoint_sq

set_option autoImplicit false

theorem ModularCurve.exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_tateToricPoint_sq
    (L : Type) [Field L] [CharZero L] (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A L] [IsFractionRing A L]
    (N : ℕ) (c : Aˣ) (hc : IsUnit (1 - (c : A))) (hc2 : IsUnit (1 - (c : A) ^ 2))
    (hcc : IsUnit ((c : A) - (c : A) ^ 2)) (hc3 : IsUnit (1 - (c : A) ^ 3)) :
    ∃ P : PowerSeries A, P.map (IsLocalRing.residue A) ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ L (P.map (algebraMap A L)) =
        (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) c)).1 -
          (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) (c ^ 2))).1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_tateToricPoint_sq.solution
