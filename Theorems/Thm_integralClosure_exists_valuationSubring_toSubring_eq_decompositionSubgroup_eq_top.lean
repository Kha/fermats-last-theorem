import Mathlib
import P2M.Util
import P2M.Sol.S_integralClosure_exists_valuationSubring_toSubring_eq_decompositionSubgroup_eq_top

set_option autoImplicit false

universe u v

theorem integralClosure.exists_valuationSubring_toSubring_eq_decompositionSubgroup_eq_top
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type v) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ 𝒜 : ValuationSubring L,
      𝒜.toSubring = (integralClosure R L).toSubring ∧
      ∃ _ : IsDiscreteValuationRing ↥𝒜,
        IsAdicComplete (IsLocalRing.maximalIdeal ↥𝒜) ↥𝒜 ∧
        Module.Finite R ↥(integralClosure R L) ∧
        (∀ r : R, algebraMap R L r ∈ 𝒜) ∧
        (∀ r : R, r ∈ IsLocalRing.maximalIdeal R →
          ∀ h : algebraMap R L r ∈ 𝒜, (⟨algebraMap R L r, h⟩ : ↥𝒜) ∈ IsLocalRing.maximalIdeal ↥𝒜) ∧
        𝒜.decompositionSubgroup K = ⊤ ∧
        (∀ σ : ↥(𝒜.decompositionSubgroup K), σ ∈ 𝒜.inertiaSubgroup K ↔
          ∀ x : ↥𝒜, ((σ • x : ↥𝒜) - x : ↥𝒜) ∈ IsLocalRing.maximalIdeal ↥𝒜) ∧

        ((∀ τ : IsLocalRing.ResidueField ↥𝒜 ≃+* IsLocalRing.ResidueField ↥𝒜,
            (∀ (r : R) (h : algebraMap R L r ∈ 𝒜),
              τ (IsLocalRing.residue ↥𝒜 ⟨algebraMap R L r, h⟩) = IsLocalRing.residue ↥𝒜 ⟨algebraMap R L r, h⟩) →
            τ = RingEquiv.refl _) →
          𝒜.inertiaSubgroup K = ⊤) := by p2m_exact_reverting @_root_.P2MW.S_integralClosure_exists_valuationSubring_toSubring_eq_decompositionSubgroup_eq_top.solution
