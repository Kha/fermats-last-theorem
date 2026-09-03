import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_conj_of_charpoly_frobenius_eq_of_absolutelyIrreducible
attribute [-instance] AlgebraicClosure.Rat.isGalois
attribute [-simp] ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

theorem GaloisRep.exists_conj_of_charpoly_frobenius_eq_of_absolutelyIrreducible
    (hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M)
    {F : Type} [Field F]
    (ρ ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ) (hfin' : GaloisFactorsThroughFiniteLevel ρ')
    (hρabs : ∀ u : Fin 2 → AlgebraicClosure F, u ≠ 0 →
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        Matrix.mulVec ((ρ σ).val.map (algebraMap F (AlgebraicClosure F))) u ∉ (AlgebraicClosure F) ∙ u)
    (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.LiesOverPrime ℓ → A.IsFrobeniusAt τ ℓ →
        (ρ τ).val.charpoly = (ρ' τ).val.charpoly) :
    ∃ g : GL (Fin 2) F, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (ρ' σ).val = g.val * (ρ σ).val * (g⁻¹).val := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_conj_of_charpoly_frobenius_eq_of_absolutelyIrreducible.solution
