import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_of_forall_mem_iff_gaussPresentation

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_of_forall_mem_iff_gaussPresentation
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
    {E : Type} [Field E] (ι : E →+* LaurentSeries L)
    (W : ValuationSubring E)
    (hW : ∀ f : E, f ∈ W ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      ι f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hne : W ≠ ⊤) :
    IsDiscreteValuationRing ↥W := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_of_forall_mem_iff_gaussPresentation.solution
