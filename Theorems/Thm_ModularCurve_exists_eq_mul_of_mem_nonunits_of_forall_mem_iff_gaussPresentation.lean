import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation

set_option autoImplicit false

theorem ModularCurve.exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∀ f : ↥K, f ∈ W₀.nonunits → ∃ g : ↥K, g ∈ W₀ ∧ f = algebraMap A ↥K ϖ * g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation.solution
