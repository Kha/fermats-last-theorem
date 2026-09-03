import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_GaloisLattice_exists_trace_det_of_basis_fin_two_of_frobenius_relations
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

open scoped TensorProduct

theorem GaloisLattice.exists_trace_det_of_basis_fin_two_of_frobenius_relations
    (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] (M : ℕ) [NeZero M] (S : Finset ℕ)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] T)
    (A : CohCarrier.Gen M (↑S : Set ℕ) → Module.End ℤ_[p] T)
    (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CohCarrier.Gen M (↑S : Set ℕ))
      (x : T), ρ σ (A g x) = A g (ρ σ x))
    (hbij : ∀ u : (ZMod M)ˣ, Function.Bijective (A (CohCarrier.Gen.dia u)))
    (hlevel : ∀ j : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ j) • y)
    (b : Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : CohCarrier.Gen M (↑S : Set ℕ) => (A g).baseChange ℚ_[p]))
      (ℚ_[p] ⊗[ℤ_[p]] T))
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
      ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ → ∀ x : T,
          A (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
              (ρ σ (ρ σ x))
            - A (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) (ρ σ x) + ℓ • x = 0)
    (hdet : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
      ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
          (A (CohCarrier.Gen.dia
              (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange ℚ_[p] *
            (↑((b.repr ((ρ σ).baseChange ℚ_[p] (b 0))) 0 * (b.repr ((ρ σ).baseChange ℚ_[p] (b 1))) 1 -
                (b.repr ((ρ σ).baseChange ℚ_[p] (b 1))) 0 * (b.repr ((ρ σ).baseChange ℚ_[p] (b 0))) 1) :
              Module.End ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)) =
            (ℓ : Module.End ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)))
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]
    (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0)
    (op : CohCarrier.Gen M (↑S : Set ℕ) → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M (↑S : Set ℕ)) (x : T), op g • x = A g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤) :
    ∃ (t d : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → 𝕋)
      (L : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)),

      t 1 = 2 ∧ d 1 = 1 ∧
      (∀ σ τ, t (σ * τ * σ⁻¹) = t τ) ∧ (∀ σ τ, d (σ * τ * σ⁻¹) = d τ) ∧
      (∀ σ τ, d (σ * τ) = d σ * d τ) ∧
      (∀ σ, t σ * t σ = t (σ * σ) + 2 * d σ) ∧
      (∀ σ (x : T), ρ σ (ρ σ x) - t σ • ρ σ x + d σ • x = 0) ∧
      (∀ σ (u : 𝕋) (x : T), ρ σ (u • x) = u • ρ σ x) ∧

      (∀ n : ℕ, FiniteDimensional ℚ (L n) ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L n, σ x = x) →
          (∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ n) • y) ∧
          (∀ τ, ∃ c : 𝕋, t (σ * τ) = t τ + (p : 𝕋) ^ n * c) ∧
          (∀ τ, ∃ c : 𝕋, d (σ * τ) = d τ + (p : 𝕋) ^ n * c)) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
            op (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
                * t σ = op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ∧
            op (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
                * d σ = (ℓ : 𝕋)) ∧

      (∀ σ, (Algebra.lsmul ℤ_[p] ℤ_[p] T (t σ)).baseChange ℚ_[p]
            = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 + b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1) ∧
          (Algebra.lsmul ℤ_[p] ℤ_[p] T (d σ)).baseChange ℚ_[p]
            = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1
                - b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 1)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisLattice_exists_trace_det_of_basis_fin_two_of_frobenius_relations.solution
