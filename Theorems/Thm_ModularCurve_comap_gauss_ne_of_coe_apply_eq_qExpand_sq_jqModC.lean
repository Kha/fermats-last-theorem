import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC

set_option autoImplicit false

open IsLocalRing

theorem ModularCurve.comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC
    (q : ℕ) [Fact q.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (φ : ↥K ≃ₐ[L] ↥K)
    (j : ↥K) (hj : (j : LaurentSeries L) = ModularCurve.jqModC L)
    (hφj : ((φ j : ↥K) : LaurentSeries L) = ModularCurve.qExpand L (q ^ 2) (ModularCurve.jqModC L)) :
    W₀.comap φ.toAlgHom.toRingHom ≠ W₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC.solution
