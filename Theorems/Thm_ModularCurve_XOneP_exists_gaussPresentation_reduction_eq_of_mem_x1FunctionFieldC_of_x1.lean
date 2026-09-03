import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_exists_gaussPresentation_reduction_eq_of_mem_x1FunctionFieldC_of_x1

set_option autoImplicit false

theorem ModularCurve.XOneP.exists_gaussPresentation_reduction_eq_of_mem_x1FunctionFieldC_of_x1
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (z : LaurentSeries (IsLocalRing.ResidueField A))
    (hz : z ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) :
    ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_exists_gaussPresentation_reduction_eq_of_mem_x1FunctionFieldC_of_x1.solution
