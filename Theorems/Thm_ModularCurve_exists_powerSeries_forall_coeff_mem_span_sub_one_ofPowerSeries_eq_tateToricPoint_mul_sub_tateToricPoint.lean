import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_powerSeries_forall_coeff_mem_span_sub_one_ofPowerSeries_eq_tateToricPoint_mul_sub_tateToricPoint

set_option autoImplicit false

theorem ModularCurve.exists_powerSeries_forall_coeff_mem_span_sub_one_ofPowerSeries_eq_tateToricPoint_mul_sub_tateToricPoint
    (L : Type) [Field L] [CharZero L] (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A L] [IsFractionRing A L]
    (N : ℕ) (c ζ' : Aˣ) (hc : IsUnit (1 - (c : A))) (hζ'c : IsUnit (1 - (ζ' : A) * (c : A))) :
    ∃ P : PowerSeries A, (∀ n : ℕ, PowerSeries.coeff n P ∈ Ideal.span {((ζ' : A) - 1)}) ∧
      HahnSeries.ofPowerSeries ℤ L (P.map (algebraMap A L)) =
        (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) (ζ' * c))).1 -
          (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) c)).1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_powerSeries_forall_coeff_mem_span_sub_one_ofPowerSeries_eq_tateToricPoint_mul_sub_tateToricPoint.solution
