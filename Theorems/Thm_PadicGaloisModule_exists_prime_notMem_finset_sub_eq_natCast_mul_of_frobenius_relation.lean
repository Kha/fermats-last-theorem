import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_PadicGaloisModule_exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation
attribute [-instance] AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem PadicGaloisModule.exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation
    {𝕋 : Type} [Ring 𝕋] (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    {A : Type} [AddCommGroup A] [Module ℤ_[p] A] [Module.Finite ℤ_[p] A] [Module.Free ℤ_[p] A]
    (φ : 𝕋 →+* Module.End ℤ_[p] A)
    (hφ : ∀ t : 𝕋, φ t ∈ Ideal.span {(p : ℤ_[p])} • Submodule.span ℤ_[p] (Set.range φ) →
      ∃ t' : 𝕋, t = (p : 𝕋) * t')
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] A)
    (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : 𝕋), ρ σ * φ t = φ t * ρ σ)
    (hcont : ∀ d : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ a : A, ρ σ a - a ∈ Ideal.span {(p : ℤ_[p])} ^ d • (⊤ : Submodule ℤ_[p] A))
    (T : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → 𝕋) (e₁ e₂ : ZMod M → 𝕋) (w : ℕ)
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          φ (T ℓ hℓ hℓM) * ρ σ =
            φ (e₁ (ℓ : ZMod M)) * (ρ σ * ρ σ) + ((ℓ : ℤ_[p]) ^ w) • φ (e₂ (ℓ : ZMod M)))
    (S : Finset ℕ) (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime) (hℓ₀M : ¬ ℓ₀ ∣ M) (hℓ₀p : ℓ₀ ≠ p) :
    ∃ (q : ℕ) (hq : q.Prime) (hqM : ¬ q ∣ M), q ∉ S ∧ q ≠ p ∧ (q : ZMod M) = (ℓ₀ : ZMod M) ∧
      ∃ t' : 𝕋, T ℓ₀ hℓ₀ hℓ₀M - T q hq hqM = (p : 𝕋) * t' := by p2m_exact_reverting @_root_.P2MW.S_PadicGaloisModule_exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation.solution
