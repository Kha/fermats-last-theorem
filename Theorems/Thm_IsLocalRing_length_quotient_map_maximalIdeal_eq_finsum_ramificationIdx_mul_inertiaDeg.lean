import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D] [Algebra C D]
    (hDmax : ∀ c : C, algebraMap C D c ∈ maximalIdeal D ↔ c ∈ maximalIdeal C)
    (hDres : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ maximalIdeal D)
    (hDdim : Ring.DimensionLEOne D) (hDnf : maximalIdeal D ≠ ⊥)
    (κ : Type*) [Field κ] [Algebra D κ] [IsFractionRing D κ] [Algebra C κ] [IsScalarTower C D κ]
    [Algebra K κ] [IsScalarTower C K κ] [FiniteDimensional K κ] [Algebra.IsSeparable K κ] :
    {B : ValuationSubring κ | ∀ d : D, algebraMap D κ d ∈ B}.Finite ∧
    Module.length D (D ⧸ (maximalIdeal C).map (algebraMap C D)) =
      ∑ᶠ B : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ d : D, algebraMap D κ d ∈ B) ∧
          ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C},
        ((letI : Algebra C ↥B.1 := ((algebraMap C κ).codRestrict B.1 B.2.1).toAlgebra
          (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B.1) * (maximalIdeal C).inertiaDeg' (maximalIdeal ↥B.1) : ℕ) : ℕ∞) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg.solution
