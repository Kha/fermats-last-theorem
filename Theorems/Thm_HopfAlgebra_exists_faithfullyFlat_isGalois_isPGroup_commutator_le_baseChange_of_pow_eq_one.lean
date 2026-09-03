import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : R))
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    (n : ℕ) (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ p ^ n = 1) :
    ∃ (R₂ : Type u) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsDiscreteValuationRing R₂) (_ : Algebra R R₂)
      (_ : Module.FaithfullyFlat R R₂) (K₂ : Type u) (_ : Field K₂) (_ : Algebra R₂ K₂) (_ : IsFractionRing R₂ K₂),
      Irreducible (p : R₂) ∧
      ∃ N : ℕ,
        (∀ s : ℕ, 0 < s → s ≤ N → ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = p ^ s →
          IsUnit ((p ^ s : R₂) - 1) ∧
            ∃ (χ : Fˣ →* R₂ˣ) (ι : F →+* IsLocalRing.ResidueField R₂),
              ∀ l : Fˣ, IsLocalRing.residue R₂ (χ l : R₂) = ι l) ∧
        Finite (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂)) ∧
        Function.Bijective
          (Algebra.TensorProduct.lift
            (Algebra.ofId (AlgebraicClosure K₂) (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) → AlgebraicClosure K₂))
            (Pi.algHom K₂ _
              fun ν : WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) =>
                (WithConv.ofConv ν : (K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂))
            (fun _ _ => Commute.all _ _) :
            AlgebraicClosure K₂ ⊗[K₂] (K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[AlgebraicClosure K₂]
              (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) → AlgebraicClosure K₂)) ∧
        Nat.card (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂)) ≤ p ^ N ∧
        (∀ ν : WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂), ν ^ p ^ n = 1) ∧
        ∃ (L : IntermediateField K₂ (AlgebraicClosure K₂)) (_ : FiniteDimensional K₂ L) (_ : IsGalois K₂ L),
          (∀ (ν : (K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) (a : (K₂ ⊗[R₂] (R₂ ⊗[R] H))), ν a ∈ L) ∧
          ∃ P : Subgroup (L ≃ₐ[K₂] L), P.Normal ∧ IsPGroup p ↥P ∧
            ∀ a b : (L ≃ₐ[K₂] L), a⁻¹ * b⁻¹ * a * b ∈ P := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one.solution
