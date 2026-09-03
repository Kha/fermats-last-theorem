import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_ringHom_valuationSubring_map_eq_zero_of_constantCoeff_mem_maximalIdeal

theorem PowerSeries.exists_ringHom_valuationSubring_map_eq_zero_of_constantCoeff_mem_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (F : PowerSeries A) (hF₀ : PowerSeries.constantCoeff F ∈ IsLocalRing.maximalIdeal A)
    (hF : PowerSeries.map (IsLocalRing.residue A) F ≠ 0)
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra A Ω] (V : ValuationSubring Ω)
    (hAV : ∀ a : A, algebraMap A Ω a ∈ V)
    (hdom : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A Ω a ∈ V.nonunits) :
    ∃ φ : PowerSeries A →+* V,
      (∀ a : A, (φ (PowerSeries.C a) : Ω) = algebraMap A Ω a) ∧
      φ PowerSeries.X ∈ IsLocalRing.maximalIdeal V ∧
      (∀ G : PowerSeries A, PowerSeries.constantCoeff G ∈ IsLocalRing.maximalIdeal A →
        φ G ∈ IsLocalRing.maximalIdeal V) ∧
      (∀ G : PowerSeries A, IsLocalRing.residue V (φ G) =
        IsLocalRing.residue V (φ (PowerSeries.C (PowerSeries.constantCoeff G)))) ∧
      IsIntegral A (φ PowerSeries.X : Ω) ∧
      (∀ G : PowerSeries A, (φ G : Ω) ∈ Algebra.adjoin A {(φ PowerSeries.X : Ω)}) ∧
      φ F = 0 := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_ringHom_valuationSubring_map_eq_zero_of_constantCoeff_mem_maximalIdeal.solution
