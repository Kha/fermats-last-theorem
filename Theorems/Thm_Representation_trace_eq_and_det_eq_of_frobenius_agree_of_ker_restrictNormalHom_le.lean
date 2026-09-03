import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_Representation_trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

theorem Representation.trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
    {k K : Type} [Field k] [Field K] [Algebra k K]
    {V₁ : Type} [AddCommGroup V₁] [Module k V₁] {V₂ : Type} [AddCommGroup V₂] [Module K V₂]
    (ρ₁ : Representation k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V₁)
    (ρ₂ : Representation K (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V₂)
    (h₁ : Module.finrank k V₁ = 2) (h₂ : Module.finrank K V₂ = 2)
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρ₁.ker ⊓ ρ₂.ker)
    (S : Finset ℕ)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          algebraMap k K (LinearMap.trace k V₁ (ρ₁ τ)) = LinearMap.trace K V₂ (ρ₂ τ))
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          algebraMap k K (LinearMap.det (ρ₁ τ)) = LinearMap.det (ρ₂ τ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    algebraMap k K (LinearMap.trace k V₁ (ρ₁ σ)) = LinearMap.trace K V₂ (ρ₂ σ) ∧
      algebraMap k K (LinearMap.det (ρ₁ σ)) = LinearMap.det (ρ₂ σ) := by p2m_exact_reverting @_root_.P2MW.S_Representation_trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le.solution
