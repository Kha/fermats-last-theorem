import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_trace_eq_of_trace_frobenius_eq
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open Polynomial IsLocalRing

theorem ResidualGaloisRep.trace_eq_of_trace_frobenius_eq
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k) (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.LiesOverPrime ℓ → A.IsFrobeniusAt τ ℓ →
        LinearMap.trace k ρ₁.V (ρ₁.ρ τ) = LinearMap.trace k ρ₂.V (ρ₂.ρ τ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.trace k ρ₁.V (ρ₁.ρ σ) = LinearMap.trace k ρ₂.V (ρ₂.ρ σ) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_trace_eq_of_trace_frobenius_eq.solution
