import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg

set_option autoImplicit false

open IsLocalRing
open scoped Pointwise

theorem ValuationSubring.exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {M : Type*} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
    [FiniteDimensional K M] [IsGalois K M]
    (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ maximalIdeal C) :
    (∀ V' : ValuationSubring M, (∀ c : C, algebraMap C M c ∈ V') →
        (∀ c : C, algebraMap C M c ∈ V'.nonunits ↔ c ∈ maximalIdeal C) →
        ∃ g : M ≃ₐ[K] M, g • V' = V) ∧
    Nat.card ↥(V.decompositionSubgroup K) =
      (letI : Algebra C ↥V := ((algebraMap C M).codRestrict V hCV).toAlgebra
       (maximalIdeal C).ramificationIdx' (maximalIdeal ↥V) *
         (maximalIdeal C).inertiaDeg' (maximalIdeal ↥V)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg.solution
