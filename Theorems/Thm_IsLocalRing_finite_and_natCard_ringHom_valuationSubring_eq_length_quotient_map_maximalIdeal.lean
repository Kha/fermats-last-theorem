import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {L : Type*} [Field L] [IsAlgClosed L] [Algebra C L] [Algebra K L] [IsScalarTower C K L] [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) (hCA : ∀ c : C, algebraMap C L c ∈ A)
    (hCAmax : ∀ c : C, (⟨algebraMap C L c, hCA c⟩ : ↥A) ∈ maximalIdeal ↥A ↔ c ∈ maximalIdeal C)
    {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D] [Algebra C D]
    (hDmax : ∀ c : C, algebraMap C D c ∈ maximalIdeal D ↔ c ∈ maximalIdeal C)
    (hDres : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ maximalIdeal D)
    (hDdim : Ring.DimensionLEOne D) (hDnf : maximalIdeal D ≠ ⊥)
    (κ : Type*) [Field κ] [Algebra D κ] [IsFractionRing D κ] [Algebra C κ] [IsScalarTower C D κ]
    [Algebra K κ] [IsScalarTower C K κ] [FiniteDimensional K κ] [Algebra.IsSeparable K κ] :
    Finite {φ : D →+* ↥A // ∀ c : C, φ (algebraMap C D c) = ⟨algebraMap C L c, hCA c⟩} ∧
    (Nat.card {φ : D →+* ↥A // ∀ c : C, φ (algebraMap C D c) = ⟨algebraMap C L c, hCA c⟩} : ℕ∞) =
      Module.length D (D ⧸ (maximalIdeal C).map (algebraMap C D)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal.solution
