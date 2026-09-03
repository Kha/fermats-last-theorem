import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField

set_option autoImplicit false

universe u v w

p2m_open "IsLocalRing~exists_valuationSubring_isDiscreteValuationRing_dominates"

theorem IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (hA : ringKrullDim A = 1)
    [Finite (ResidueField A)]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type w} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L] :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing ↥V ∧
      (∀ a : A, algebraMap A L a ∈ V) ∧
      (∀ a : A, a ∈ maximalIdeal A ↔ algebraMap A L a ∈ V.nonunits) ∧
      Finite (ResidueField ↥V) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField.solution
