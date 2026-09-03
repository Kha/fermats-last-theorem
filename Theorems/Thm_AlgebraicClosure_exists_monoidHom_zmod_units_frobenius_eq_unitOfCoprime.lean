import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem AlgebraicClosure.exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime
    (L : ℕ) [NeZero L] :
    ∃ (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ)
      (F : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ F ∧
      (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, τ x = x) → χ τ = 1) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L)
        (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          χ σ = ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime.solution
