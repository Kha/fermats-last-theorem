import Mathlib
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_MonoidHom_exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

theorem MonoidHom.exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (M : ℕ) [NeZero M] (χ : (ZMod M)ˣ →* kˣ) :
    ∃ ψ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* kˣ,
      IsOpen ((ψ.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∧
      ψ complexConjugation = -χ (-1) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            (ψ σ : k) = (ℓ : k) *
              (χ (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)) : k) := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul.solution
