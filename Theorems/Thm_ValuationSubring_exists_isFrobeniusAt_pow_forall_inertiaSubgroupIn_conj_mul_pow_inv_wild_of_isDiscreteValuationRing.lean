import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild_of_isDiscreteValuationRing

set_option autoImplicit false

theorem ValuationSubring.exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild_of_isDiscreteValuationRing
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤)
    (F : IntermediateField K Ω) [FiniteDimensional K ↥F] :
    ∃ (d : ℕ) (φ : Ω ≃ₐ[K] Ω), 0 < d ∧ (∀ z ∈ F, φ z = z) ∧ A.IsFrobeniusAt φ (p ^ d) ∧
      ∀ τ : Ω ≃ₐ[K] Ω, τ ∈ A.inertiaSubgroupIn K →
        φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹ ∈ A.inertiaSubgroupIn K ∧
        (∀ z : Ω, z ≠ 0 → (φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹) z * z⁻¹ - 1 ∈ A.nonunits) ∧
        ∀ (F' : IntermediateField K Ω) [FiniteDimensional K ↥F'] [Normal K ↥F'],
          ∃ a : ℕ, ∀ x ∈ F', ((φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹) ^ (p ^ a)) x = x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild_of_isDiscreteValuationRing.solution
