import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {L : Type*} [Field L] [IsAlgClosed L] [Algebra C L] [Algebra K L] [IsScalarTower C K L] [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) (hCA : ∀ c : C, algebraMap C L c ∈ A)
    (hCAmax : ∀ c : C, (⟨algebraMap C L c, hCA c⟩ : ↥A) ∈ maximalIdeal ↥A ↔ c ∈ maximalIdeal C)
    (κ : Type*) [Field κ] [Algebra K κ] [Algebra C κ] [IsScalarTower C K κ] [FiniteDimensional K κ] [Algebra.IsSeparable K κ]
    (B : ValuationSubring κ) (hCB : ∀ c : C, algebraMap C κ c ∈ B)
    (hCBmax : ∀ c : C, (⟨algebraMap C κ c, hCB c⟩ : ↥B) ∈ maximalIdeal ↥B ↔ c ∈ maximalIdeal C) :
    Finite {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B} ∧
    Nat.card {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B} =
      (letI : Algebra C ↥B := ((algebraMap C κ).codRestrict B hCB).toAlgebra
       (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B) * (maximalIdeal C).inertiaDeg' (maximalIdeal ↥B)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg.solution
