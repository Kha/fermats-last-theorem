import Mathlib
import P2M.Util
import P2M.Sol.S_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring

set_option autoImplicit false

universe u

theorem IsNoetherianRing.exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ) (hn : IsUnit ((n : ℕ) : R))
    (c : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω], (R →+* Ω) → Ω)
    (hc : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), c Ω φ ^ n = 1)
    (hv : ∀ (K : Type u) [Field K] [IsAlgClosed K] (𝒪 : ValuationSubring K)
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ρ : R →+* 𝒪) (ψ : 𝒪 →+* Ω),
      ∃ u : 𝒪, c K ((algebraMap 𝒪 K).comp ρ) = algebraMap 𝒪 K u ∧ c Ω (ψ.comp ρ) = ψ u) :
    ∃ ε : R, ε ^ n = 1 ∧ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), c Ω φ = φ ε := by p2m_exact_reverting @_root_.P2MW.S_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring.solution
