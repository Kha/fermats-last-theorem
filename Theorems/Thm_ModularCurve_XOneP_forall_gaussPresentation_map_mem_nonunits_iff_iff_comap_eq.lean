import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq

set_option autoImplicit false

theorem ModularCurve.XOneP.forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq
    (A : Type*) [CommRing A] [IsLocalRing A] (L : Type*) [Field L] [Algebra A L]
    (K : IntermediateField L (LaurentSeries L))
    (W₀ W₁ : ValuationSubring ↥K)
    (h4 : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (h6 : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (K' : Type*) [Field K'] (ι : ↥K →+* K') (V : ValuationSubring K')
    (hV : V.comap ι = W₀ ∨ V.comap ι = W₁) :
    (∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (ι f ∈ V.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) ↔
      V.comap ι = W₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq.solution
