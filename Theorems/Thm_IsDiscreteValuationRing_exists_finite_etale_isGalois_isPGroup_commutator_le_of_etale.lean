import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem IsDiscreteValuationRing.exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale
    {R₁ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
    [IsAdicComplete (IsLocalRing.maximalIdeal R₁) R₁]
    (K₁ : Type u) [Field K₁] [Algebra R₁ K₁] [IsFractionRing R₁ K₁] [CharZero K₁]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : R₁)) (N : ℕ)
    (B₁ : Type v) [CommRing B₁] [Algebra K₁ B₁] [Module.Finite K₁ B₁] [Algebra.Etale K₁ B₁] :
    ∃ (R₂ : Type u) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsDiscreteValuationRing R₂)
      (_ : Algebra R₁ R₂) (_ : Module.Finite R₁ R₂) (_ : Module.Free R₁ R₂) (_ : Module.FaithfullyFlat R₁ R₂)
      (K₂ : Type u) (_ : Field K₂) (_ : Algebra R₂ K₂) (_ : IsFractionRing R₂ K₂)
      (_ : Algebra K₁ K₂) (_ : Algebra R₁ K₂) (_ : IsScalarTower R₁ R₂ K₂) (_ : IsScalarTower R₁ K₁ K₂),
      Irreducible (p : R₂) ∧ IsLocalHom (algebraMap R₁ R₂) ∧
      (∀ s : ℕ, 0 < s → s ≤ N → ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = p ^ s →
        IsUnit ((p ^ s : R₂) - 1) ∧
          ∃ (χ : Fˣ →* R₂ˣ) (ι : F →+* IsLocalRing.ResidueField R₂),
            ∀ l : Fˣ, IsLocalRing.residue R₂ (χ l : R₂) = ι l) ∧
      ∃ (L : IntermediateField K₂ (AlgebraicClosure K₂)) (_ : FiniteDimensional K₂ L) (_ : IsGalois K₂ L),
        (∀ (ν : K₂ ⊗[K₁] B₁ →ₐ[K₂] AlgebraicClosure K₂) (b : K₂ ⊗[K₁] B₁), ν b ∈ L) ∧
        ∃ P : Subgroup (L ≃ₐ[K₂] L), P.Normal ∧ IsPGroup p ↥P ∧
          ∀ a b : (L ≃ₐ[K₂] L), a⁻¹ * b⁻¹ * a * b ∈ P := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale.solution
