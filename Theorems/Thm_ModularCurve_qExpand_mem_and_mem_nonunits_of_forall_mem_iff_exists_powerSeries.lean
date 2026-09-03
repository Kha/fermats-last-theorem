import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_mem_and_mem_nonunits_of_forall_mem_iff_exists_powerSeries

set_option autoImplicit false

theorem ModularCurve.qExpand_mem_and_mem_nonunits_of_forall_mem_iff_exists_powerSeries
    (L : Type) [Field L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L]
    (W₀ : ValuationSubring ↥K)
    (h1 : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (h5 : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (N : ℕ) [NeZero N] (f : ↥K) (hfN : ModularCurve.qExpand L N (f : LaurentSeries L) ∈ K) :
    (f ∈ W₀ → (⟨ModularCurve.qExpand L N (f : LaurentSeries L), hfN⟩ : ↥K) ∈ W₀) ∧
    (f ∈ W₀.nonunits → (⟨ModularCurve.qExpand L N (f : LaurentSeries L), hfN⟩ : ↥K) ∈ W₀.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_mem_and_mem_nonunits_of_forall_mem_iff_exists_powerSeries.solution
