import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_valuationSubring_eq_of_finrank_le_finrank_residueField

set_option autoImplicit false

theorem IsDiscreteValuationRing.valuationSubring_eq_of_finrank_le_finrank_residueField
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (W : ValuationSubring F) (hW : W ≠ ⊤) (hOW : ∀ x : O, algebraMap O F x ∈ W)
    (hmW : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O F x ∈ W.nonunits)

    [Algebra O ↥W] (halg : ∀ x : O, ((algebraMap O ↥W x : ↥W) : F) = algebraMap O F x)
    [Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField ↥W)]
    (hres : ∀ x : O, algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField ↥W)
      (IsLocalRing.residue O x) = IsLocalRing.residue ↥W (algebraMap O ↥W x))
    (hf : Module.finrank E F ≤ Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField ↥W)) :
    ∀ W' : ValuationSubring F, W' ≠ ⊤ → (∀ x : O, algebraMap O F x ∈ W') →
      (∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O F x ∈ W'.nonunits) → W' = W := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_valuationSubring_eq_of_finrank_le_finrank_residueField.solution
